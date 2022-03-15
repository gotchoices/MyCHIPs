//Improved agent-based model; Limited testing for distributed network
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- Don't assume agent CID is unique across population (using CID as unique array key)
//- Make decisions like:
//-   Establishing new tallies (both stock and foil)
//-   Closing old tallies?
//-   Paying people down-stream of me
//-   Setting trading parameters (target,reward,clutch,bound)
//-   Establishing buy/sell orders
//-   When do I need more income
//-   When do I want to buy more things
//- 
const { dbClient } = require('wyseman')			//Connection to SQL
const Os = require('os')
const DocClient = require('mongodb').MongoClient	//Connection to doc DB
const MongoOpts = { useNewUrlParser: true, useUnifiedTopology: true }
const { Log } = require('wyclif')
const uuidv4 = require('uuid/v4')
//const userFields = ['id', 'std_name', 'peer_cid', 'serv_id']		Not used anymore?
const parmQuery = "select parm,value from base.parm_v where module = 'agent'"	//Operating parameters

const userSql = `select id, std_name, ent_name, fir_name, ent_type, user_ent,
	peer_cid, peer_cagent, peer_chost, peer_cport, 
	stocks, foils, partners, vendors, clients,
	vendor_cids, client_cids, stock_seqs, foil_seqs, units, types, seqs, targets
	from mychips.users_v_tallysum
	where not peer_ent isnull`
const peerSql = `insert into mychips.peers_v 
	(ent_name, fir_name, ent_type, born_date, peer_cid, peer_agent, peer_host, peer_port) 
	values ($1, $2, $3, $4, $5, $6, $7, $8) returning *`

// -----------------------------------------------------------------------------
module.exports = class AgentCluster {
  constructor(sqlConfig, docConfig, argv) {
    this.log = Log('agent')

    let dbConf = Object.assign({
      log: this.log,
      listen: ['parm_agent', 'mychips_admin', 'mychips_user'],		//Asynchronous message from DB
    }, sqlConfig)

    this.host = argv.peerServer || Os.hostname()
    this.log.info('Initializing agent model controller 2 on:', this.host)
    this.parms = {
      interval: argv.interval || 2000, 
      addclient: 0.10,			//Try to add client 10% of the time
      checksets: 0.50,			//Try to adjust settings 50% of the time
      addvendor: 0.40,			//Try to add vendors 15% of the time (not yet implemented)
      maxstocks: 2,
      maxfoils: 3,
      mintotpay: -10000,		//Make payments if net worth greater than this
      maxtopay: 0.10,			//Pay up to 10% of my net worth
      maxtarget: 100
    }
    this.agents = []

    this.remoteIdx = 0		//Use to make unique tag for each remote command
    this.remoteCBs = {}		//Store routines to call on completion
    
    this.agent = null		//Keep track of which user we are processing
    this.counter = 0
    if (argv.runs) {this.runs = argv.runs}			//Max iterations
    this.sqlDB = new dbClient(dbConf, (channel, payload) => {	//Initialize Database connection
      let msg
      this.log.trace('Agent DB async on:', channel, 'payload:', payload)
      if (payload) try {msg = JSON.parse(payload)} catch(e) {log.error("Parsing json payload: " + payload)}

      if (channel == 'parm_agent') {				//Parameter updated
        this.log.debug("Parameter", msg.target, "=", msg.value, msg)
        if (msg.target in this.parms && msg.value) this.parms[msg.target] = msg.value

      } else if (channel == 'mychips_admin') {			//Something in the user data has changed
        if (msg.target == 'peers' || msg.target == 'tallies') {
          this.sqlDB.query(userSql + " and latest >= $1", [msg.time], (e,r)=>{this.eatAgents(e,r)})
        }

      } else if (channel == 'mychips_user') {			//Respond as a real user would to a request/event
        if (msg.target == 'tally') this.tallyState(msg)
      }
    })
    this.intervalTimer = null
    this.sqlDB.query(parmQuery, (e,r)=>{this.eatParms(e,r)})	//Load initial parameters
    
    let url = `mongodb://${docConfig.host}:${docConfig.port}/?replicaSet=rs0`
    this.log.verbose("Mongo:", this.host, url)
//    this.worldPop = 40					//Init to any reasonable value
    this.docClient = new DocClient(url, MongoOpts)
    this.docClient.connect((err, client) => {			//Connect to mongodb
      if (err) {this.log.error('in Doc DB connect:', err.stack); return}
      this.docDB = client.db(docConfig.database)		//Pointer to DB connection

      this.docAc = this.docDB.collection("actions")		//Pointer to actions collection
//      this.docAcStream = this.docAc.watch([{$match: { host: null }}])
      this.docAcStream = this.docAc.watch([{$match: { 'fullDocument.host': this.host }}])	//Receive async updates for this host
      this.docAcStream.on('error', ev=>{this.log.error("Couldn't watch mongo:", this.host, ev)})

      this.docAcStream.on('change', ev=>{		//Handle async notices from doc DB
        let doc = ev ? ev.fullDocument : {}
this.log.debug("Got doc change:", doc.action, doc.host, doc.data)
        if (doc.action == 'createUser') {		//Someone asking me to insert a peer into the DB
          this.checkPeer(doc.data, pDat=>{
this.log.debug("Peer added/OK:", pDat.peer_cid, "notifying:", doc.data.host)
            this.docAc.insertOne({action: 'done', tag:doc.tag, host:doc.data.host, from:this.host}, ()=>{})
          })
        } else if (doc.action == 'done') {		//Remote action has completed
this.log.debug("Remote call done:", doc.tag, "from:", doc.from)
          if (this.remoteCBs[doc.tag]) {		//If I can find a stored callback
            this.remoteCBs[doc.tag]()			//Call it
            delete this.remoteCBs[doc.tag]		//And then forget about it
          }
        }
        this.docAc.deleteOne({_id: doc._id})		//Delete signaling record
      })
      
      this.docAg = this.docDB.collection("agents")	//Pointer to agents collection
//      this.docAg.createIndex({peer_cid: 1}, {unique: true})		//Should be multicolumn: cid, host
//      this.docAg.countDocuments((e,r)=>{if (!e) this.worldPop = r})	//Actual people in doc DB
      this.log.trace("Connected to doc DB")
      this.sqlDB.query(userSql, (e,r)=>{this.eatAgents(e,r,true)})	//Load up initial set of users
    })
  }	//Constructor

// -----------------------------------------------------------------------------
  remoteCall(host, cmd, data, cb) {			//Execute command on foreign peer
    let tag = host + '.' + this.remoteIdx++		//Make unique message ID
this.log.debug("Remote calling:", cmd, "to:", host)
    this.remoteCBs[tag] = cb				//Remember function to call locally on completion
    this.docAc.insertOne({action: cmd, tag, host, from: this.host, data}, null, (err, res)=>{
      if (err) this.log.error("Sending remote command:", cmd, "to:", host)
    })
  }

// -----------------------------------------------------------------------------
  eatAgents(err, res, all) {					//Freshly load agent data from database
    if (err) {this.log.error('In query:', err.stack); return}
    if (!this.docDB) return					//Ingore until document db connected/ready
    this.log.trace('Loaded agents:', res.rows.length)
    let haveEm = []						//Keep track of which ones we've processed

    res.rows.forEach( row => {				//For each agent in sql result
      let aIdx = this.agents.findIndex(el=>(el.peer_cid == row.peer_cid))	//find him in my local list
      if (aIdx >= 0) this.agents[aIdx] = row; else this.agents.push(row)	//Keep local copy, maybe replacing old copy
      if (row.user_ent) {				//If this is one we host, update world db
        haveEm.push(row.peer_cid)
        row.random = Math.random()			//Will help later in random selections
        row.host = this.host				//Mark user as belonging to us
        this.docAg.updateOne({peer_cid: row.peer_cid, host: row.host}, {$set: row}, {upsert: true}, (e,r)=>{
          if (e) this.log.error(e.message)
          else this.log.trace("Add/update agent:", r)
        })
      }
    })

    if (all) this.docAg.deleteMany({			//Delete any strays left in world db
      host: this.host,
      peer_cid: {$nin: haveEm}				//Anyone not in our recent batch deleted
    }, (e,r) => {
      if (e) this.log.error(e.message)
      else this.log.debug("Delete agents in world:", r.n)
    })
    
    if (!this.agent && this.agents.length > 0) this.agent = 0	//Initialize loop to traverse agents
  }
  
// -----------------------------------------------------------------------------
  eatParms(err, res) {						//Digest operating parameters from database
    this.log.trace("eatParms")
    if (err) {this.log.error('In query:', err.stack); return}
    res.rows.forEach((row) => {
      let { parm, value } = row
      this.parms[parm] = value
    })

    if (this.intervalTimer) clearInterval(this.intervalTimer)	//Restart interval timer
    this.intervalTimer = setInterval(()=>{
      if (this.agent != null && (!this.runs || this.counter < this.runs)) 
        this.process(++this.counter)
    }, this.parms.interval)
  }
  
// -----------------------------------------------------------------------------
  close() {							//Shut down this simulation
    this.log.debug("Shutting down agent handler")
    if (this.sqlDB.client.activeQuery) {			//If there is a query in process
      setTimeout(this.close, 500)				//Try again in a half second
    } else {
      this.sqlDB.disconnect()
    }
    if (this.intervalTimer) clearInterval(this.intervalTimer)
  }

// -----------------------------------------------------------------------------
  process(run) {						//Iterate on a single agent
    let aData = this.agents[this.agent]				//Point to agent's data
      , actSpace = Math.random()				//Randomize what action we will take
      , startAgent = this.agent
    while (!aData.user_ent) {					//Find a local user
      if (++this.agent >= this.agents.length) this.agent = 0	//Loop around
      this.log.trace("  Skipping non-local partner:", this.agent, startAgent)
      if (this.agent == startAgent) return			//Avoid infinite loop if no users found
      aData = this.agents[this.agent]
    }
    this.log.verbose("Handler", run, this.agent, "of", this.agents.length, aData.id, aData.std_name, aData.peer_cid)
    if (++this.agent >= this.agents.length) this.agent = 0	//Will go to next agent next time

this.log.debug("  stocks:", aData.stocks, this.parms.maxstocks, "  foils:", this.parms.maxfoils, "space:", actSpace)
    if (aData.stocks <= 0 || (actSpace < this.parms.addclient && aData.stocks < this.parms.maxstocks)) {	//I don't have any, or enough clients (or jobs)
      this.docAg.findOneAndUpdate({			//Look for a trading partner
        peer_cid: {
          $ne: aData.peer_cid,				//Don't find myself
          $nin: aData.partners				//Or anyone I'm already connected to
        },
//        host: {$ne: this.host},			//Look only on other hosts
        foils: {$lte: this.parms.maxfoils},		//Or those with not too many foils already
      }, {
        $set: {random: Math.random()},			//re-randomize this person
        $inc: {foils: 1},				//And make it harder to get them again next time
        $push: {partners: aData.peer_cid}		//Immediately add ourselves to the array to avoid double connecting
      }, {						//Sort by
        sort: {foils: 1, random: -1}
      }, (e, res) => {					//Get result of query
        if (e) {
          this.log.error(e.errmsg)
        } else if (res.ok) {
this.log.verbose("  Best client:", res.value.std_name, res.value.host)
          this.tryTally(aData, res.value)
        } else {
this.log.verbose("  No client found in world DB")
        }
      })	//findOneAndUpdate

    } else if (actSpace < this.parms.checksets && aData.targets.some((el,ix) => {	//Time to check settings?
      return !parseInt(el) && aData.types[ix] == 'foil'
    	})) {				//Could do something more interesting with channel settings
      this.log.debug("  Set targets:", aData.targets)
      this.chkSettings(aData)

//    } else if (aData.foils <= 0 || actSpace < this.parms.addvendor) {			//I don't have any vendors, places to buy things
//      let vendors = this.agents.slice(0).sort((a,b)=>{return a.stocks - b.stocks})	//Sort potential vendors by how many vendors they have
//        , vdIdx = Math.floor(Math.random() * vendors.length / 4)			//Look in the first 25% of sort
//        , vData
//      for(vData = vendors[vdIdx]; vdIdx < vendors.length; vData = vendors[vdIdx++])
//        if (aData.id != vData.id && !aData.partners.includes(vData.id)) break		//Don't link to myself or the same person twice
//      this.log.debug("  attempt to ask:", vData.std_name, "to be my vendor", vData.stocks, aData.foils, vdIdx)
//      if (vdIdx < vendors.length && vData.stocks < 2 && aData.foils < 4)
//        this.createTally(vData, aData)

    } else if (aData.foils > 0 && aData.units > this.parms.mintotpay) {		//Time to make a payment
      let vIdx = Math.floor(Math.random() * aData.foils)
        , vId = aData.vendors[vIdx]
        , vData = vId ? this.agents.find(el=>(el.id == vId)) : null
      this.log.debug("  I:", aData.id, "; Pay a vendor", vIdx, 'of', aData.vendors.length, vId, "NW:", aData.units)
      if (vData) this.payVendor(aData, vIdx, vData)
    }
  }

// -----------------------------------------------------------------------------
  tryTally(aData, pDoc) {			//Try to request tally from someone in the world
this.log.debug("  Try tally:", aData.peer_cid, 'with', pDoc.peer_cid)
    this.checkPeer(pDoc, (pData, hadEm)=>{
      let host = pDoc.peer_chost

      this.remoteCall(host, 'createUser', aData, ()=>{	//Insert this peer remotely
        let uuid = uuidv4()
          , sig = "Valid"
          , contract = {name: "mychips-0.99"}
          , tallySql = "insert into mychips.tallies_v (tally_ent, tally_uuid, partner, hold_sig, contract, request) values ($1, $2, $3, $4, $5, $6);"
          , partner = 'test'

this.log.debug("Tally request:", tallySql, aData.id, pData.id)
        this.sqlDB.query(tallySql, [aData.id, uuid, pData.id, sig, contract, 'draft'], (err,res) => {
          if (err) {this.log.error('In query:', err.stack); return}
          this.log.debug("  Initial tally by:", aData.std_name, " with partner:", pData.std_name)
          aData.stocks++
//          pData.foils++
        })
      })
    })
  }

// Check to see if a peer is in our system, if not add them and then do cb
// -----------------------------------------------------------------------------
  checkPeer(pData, cb) {			//Make sure we have a peer in our system
    let host, port
      , aData = this.agents.find(el=>(el.peer_cid == pData.peer_cid))
//    if (pData.peer_sock) {[ host, port ] = pData.peer_sock.split(':')}		//If default socket, use it for host,port

this.log.debug("Checking if we have peer:", pData.peer_cid, !!aData)
    if (aData)					//Found him, do the callback
      cb(aData, true)
    else if (pData.host == this.host)		//We should always have all local users
      this.log.error("Should have had local user:", pData.peer_cid)

    else this.sqlDB.query(peerSql, [pData.ent_name, pData.fir_name, pData.ent_type, pData.born_date, pData.peer_cid, pData.peer_cagent, pData.peer_chost, pData.peer_cport], (err,res) => {
      if (err) {this.log.error('Adding peer:', pData.peer_cid, err.stack); return}
      let newGuy = res.rows[0]
      this.log.debug("  Inserting partner locally:", newGuy.std_name, newGuy.peer_sock)
      this.agents.push(newGuy)
      cb(newGuy)
    })
  }

// -----------------------------------------------------------------------------
  tallyState(msg) {			//Someone is asking an agent to act on a tally
this.log.debug('Peer Message:', msg)

    if (msg.state == 'peerProffer') {	//For now, we will always answer 'yes'
this.log.verbose('  peerProffer:', msg.entity)
      this.sqlDB.query("update mychips.tallies_v set request = 'open' where tally_ent = $1 and tally_seq = $2", [msg.entity, msg.sequence], (e,r) => {
        if (e) {this.log.error('In :', e.stack); return}
//        let row = r.rows && r.rows.length >= 1 ? r.rows[0] : null
//          , aData = this.agents.findIndex(el=>(el.peer_cid == row.peer_cid))
        this.log.verbose('  Tally affirmed:', msg.object)
      })
    }
  }

// -----------------------------------------------------------------------------
  payVendor(aData, vIdx, vData) {
    let uuid = uuidv4()
      , sig = "Valid"							//Dummy signature
      , max = Math.max(aData.units * this.parms.maxtopay, 1000)		//Pay 1 CHIP or % of net worth
      , units = Math.floor(Math.random() * max)				//Random payment amount
      , seq = aData.foil_seqs[vIdx]					//Tally sequence
      , quid = 'Inv' + Math.floor(Math.random() * 1000)			//Invoice number
      , req = 'userDraft'						//request
      , sql = "insert into mychips.chits_v (chit_ent,chit_seq,chit_uuid,chit_type,signature,units,quidpro,request) values ($1,$2,$3,'tran',$4,$5,$6,$7)"

this.log.verbose("  payVendor:", aData.id, "->", vData.id, "on:", seq, "Units:", units)
    this.sqlDB.query(sql, [aData.id,seq,uuid,sig,units,quid,req], (e,r) => {
      if (e) {this.log.error('In payment:', e.stack); return}
      this.log.debug("  payment:", aData.id, aData.std_name, "to:", vData.id, vData.std_name)
    })
  }

// -----------------------------------------------------------------------------
  chkSettings(aData) {				//Adjust tally settings
    let sqls = []
      , i = 0

    aData.targets.forEach(t=>{
      let seq = aData.seqs[i]
        , ent = aData.id
        , newTarg = parseInt(Math.random() * this.parms.maxtarget)
        , newBound = parseInt(Math.random() * newTarg * 0.50) + newTarg
        , reward = parseInt(Math.random() * 5)/100 + 0.05
      this.log.trace("   seq:", seq, "type:", aData.types[i])
      if (aData.types[i] == 'foil') {		//For now, we will assert settings only on foil tallies
        sqls.push(`insert into mychips.tally_sets (tset_ent, tset_seq, target, bound, reward, signature) values ('${ent}', ${seq}, ${newTarg}, ${newBound}, ${reward}, 'Valid')`)
      }
      i++
    })
    this.log.debug("  Settings:", sqls.join(';'))
    this.sqlDB.query(sqls.join(';'), null, (e,r) => {
      if (e) {this.log.error('In settings:', e.stack); return}
    })
  }

}		//class AgentCont


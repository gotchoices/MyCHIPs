//Improved agent-based model; Limited testing for distributed network
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//X- My transactions should reach across databases now
//- callBacks is messy, make function module that sends commands to peer servers
//-   send transaction ID to remote
//-   confirmation comes back using same ID
//-   store callback in array indexed by transaction ID
//- Can I begin to model distributed lift now?
//- Do I need to listen to mychips_user_<host_id>?
//- 
//- From version 1:
//- Make decisions like:
//-   Establishing new tallies (stock and foil)
//-   Closing old tallies?
//-   Paying people down-stream of me
//-   Establishing buy/sell orders
//- 
const { dbClient } = require('wyseman')
const Os = require('os')
const DocClient = require('mongodb').MongoClient
const MongoOpts = { useNewUrlParser: true, useUnifiedTopology: true }
const { Log } = require('wyclif')
const uuidv5 = require('uuid/v5')
const userFields = ['id', 'std_name', 'peer_cid', 'host_id']
const parmQuery = "select parm,value from base.parm_v where module = 'agent'"

const userSql = `select id, std_name, ent_name, fir_name, ent_type, user_ent,
	peer_cid, peer_sock, stocks, foils, partners, vendors, clients,
	vendor_cids, client_cids, stock_seqs, foil_seqs
	from mychips.users_v_tallysum
	where not peer_ent isnull`
const peerSql = `insert into mychips.peers_v 
	(ent_name, fir_name, ent_type, born_date, peer_cid, peer_host, peer_port) 
	values ($1, $2, $3, $4, $5, $6, $7) returning *`

// -----------------------------------------------------------------------------
module.exports = class AgentCluster {
  constructor(sqlConfig, docConfig, argv) {
    this.log = Log('agent2')

    let dbConf = Object.assign({
      log: this.log,
      listen: ['parm_agent', 'mychips_admin', 'mychips_user'],
    }, sqlConfig)

    this.host = Os.hostname()
    this.log.info('Initializing agent model controller 2 on:', this.host)
    this.parms = {interval: argv.interval || 1000, addclient: 0.10, addvendor: 0.20}
    this.agents = []
    this.callBacks = []
    this.agent = null
    this.counter = 0
    if (argv.runs) {this.runs = argv.runs}			//Max iterations
    this.sqlDB = new dbClient(dbConf, (channel, payload) => {	//Initialize Database connection
      var msg
      this.log.debug('Agent DB async on:', channel, 'target:', payload.target)
      if (payload) try {msg = JSON.parse(payload)} catch(e) {log.error("Parsing json payload: " + payload)}
      if (channel == 'parm_agent') {
        this.log.debug("Parameter", msg.target, "=", msg.value, msg)
        if (msg.target in this.parms && msg.value) this.parms[msg.target] = msg.value

      } else if (channel == 'mychips_admin') {
        if (msg.target == 'peers' || msg.target == 'tallies') {
          this.sqlDB.query(userSql + " and latest >= $1", [msg.time], (e,r)=>{this.eatAgents(e,r)})
        }
      } else if (channel == 'mychips_user') {
        if (msg.target == 'tally') this.tallyState(msg)
      }
    })
    this.intervalTimer = null
    this.sqlDB.query(parmQuery, (e,r)=>{this.eatParms(e,r)})
    
    let url = `mongodb://${docConfig.host}:${docConfig.port}/?replicaSet=rs0`
    this.log.verbose("Mongo:", this.host, url)
//    this.worldPop = 40					//Init to any reasonable value
    this.docClient = new DocClient(url, MongoOpts)
    this.docClient.connect((err, client) => {
      if (err) {this.log.error('in Doc DB connect:', err.stack); return}
      this.docDB = client.db(docConfig.database)

      this.docAc = this.docDB.collection("actions")
//      this.docAcStream = this.docAc.watch([{$match: { host: null }}])
      this.docAcStream = this.docAc.watch([{$match: { 'fullDocument.host': this.host }}])
      this.docAcStream.on('error', ev=>{this.log.error("Couldn't watch mongo:", this.host, ev)})
      this.docAcStream.on('change', ev=>{
        let doc = ev ? ev.fullDocument : {}
this.log.debug("Got change:", doc.action, doc.host, doc.peer.peer_cid, doc.peer.peer_sock)
        if (doc.action == 'createUser') {		//Someone asking me to insert a peer into the DB
          this.checkPeer(doc.peer, pDat=>{
this.log.debug("Peer added/OK:", pDat.peer_cid, "notifying:", doc.peer.host)
            this.docAc.deleteOne({_id: doc._id})
            this.docAc.insertOne({action: 'userCreated', host:doc.peer.host, from:this.host, peer:doc.peer}, ()=>{})
          })
        } else if (doc.action == 'userCreated') {
          let peer = doc.peer.peer_cid
            , host = doc.from
this.log.debug("User creation done:", peer, "on:", host)
          if (this.callBacks[peer] && this.callBacks[peer][host]) {
            this.callBacks[peer][host]()		//Call handler if it exists
            this.register(peer,host)			//And deregister
          }
        }
      })
      
      this.docAg = this.docDB.collection("agents")
//      this.docAg.createIndex({peer_cid: 1}, {unique: true})		//Should be multicolumn: cid, host
//      this.docAg.countDocuments((e,r)=>{if (!e) this.worldPop = r})	//Actual people in doc DB
      this.log.trace("Connected to doc DB")
      this.sqlDB.query(userSql, (e,r)=>{this.eatAgents(e,r,true)})
    })
  }	//Constructor

// -----------------------------------------------------------------------------
  register(peer, host, cb) {		//Register callbacks to be done when a remote user has been created
//this.log.debug("Registering callback:", peer, host, !!cb)
    if (!this.callBacks[peer]) this.callBacks[peer] = {}
    if (!this.callBacks[peer][host]) this.callBacks[peer][host] = cb
  }

// -----------------------------------------------------------------------------
  eatAgents(err, res, all) {					//Freshly load agent data from database
    if (err) {this.log.error('In query:', err.stack); return}
    if (!this.docDB) return					//Document db connected/ready
    this.log.debug('Loaded agents:', res.rows.length)
    let haveEm = []						//Keep track of which ones we've processed

    res.rows.forEach( row => {				//For each agent in sql
      let aIdx = this.agents.findIndex(el=>(el.peer_cid == row.peer_cid))
      if (aIdx >= 0) this.agents[aIdx] = row; else this.agents.push(row)	//Keep local copy
      if (row.user_ent) {				//If this is one we host, update world db
        haveEm.push(row.peer_cid)
        row.random = Math.random()
        row.host = this.host				//Mark user as belonging to us
        this.docAg.updateOne({peer_cid: row.peer_cid, host: row.host}, {$set: row}, {upsert: true}, (e,r)=>{
          if (e) this.log.error(e.message)
          else this.log.trace("Add/update agent:", r)
        })
      }
    })

    if (all) this.docAg.deleteMany({			//Delete any strays left in world db
      host: this.host,
      peer_cid: {$nin: haveEm}
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
  close() {							//Shut down this controller
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
    let aData = this.agents[this.agent]
      , actSpace = Math.random()
    this.log.verbose("Handler", run, this.agent, "of", this.agents.length, aData.id, aData.std_name, aData.peer_cid)
    if (++this.agent >= this.agents.length) this.agent = 0	//Will go to next agent next time
    if (!aData.user_ent) {
      this.log.trace("  Skipping non-local partner:", aData.peer_cid)
      return
    }
this.log.debug("  stocks:", aData.stocks)
    if (aData.stocks <= 0 || (actSpace < this.parms.addclient && aData.stocks < 2)) {	//I don't have any, or enough clients (or jobs)
      this.docAg.findOneAndUpdate({			//Look for a trading partner
        peer_cid: {
          $ne: aData.peer_cid,				//Don't find myself
          $nin: aData.partners				//Or anyone I'm already connected to
        },
//        host: {$ne: this.host},			//Look only on other hosts
        foils: {$lt: 4},				//Or those with lots of foils already
      }, {
        $set: {random: Math.random()},			//re-randomize this person
        $inc: {foils: 1}				//And make it harder to get them next time
      }, {						//Sort by
        sort: {foils: 1, random: -1}
      }, (e, res) => {
        if (e) {
          this.log.error(e.errmsg)
        } else if (res.ok) {
this.log.verbose("  Best client:", res.value.std_name, res.value.host)
          this.tryTally(aData, res.value)
        } else {
this.log.verbose("  No client found in world DB")
        }
      })

//    } else if (aData.foils <= 0 || actSpace < this.parms.addvendor) {			//I don't have any vendors, places to buy things
//      let vendors = this.agents.slice(0).sort((a,b)=>{return a.stocks - b.stocks})	//Sort potential vendors by how many vendors they have
//        , vdIdx = Math.floor(Math.random() * vendors.length / 4)			//Look in the first 25% of sort
//        , vData
//      for(vData = vendors[vdIdx]; vdIdx < vendors.length; vData = vendors[vdIdx++])
//        if (aData.id != vData.id && !aData.partners.includes(vData.id)) break		//Don't link to myself or the same person twice
//      this.log.debug("  attempt to ask:", vData.std_name, "to be my vendor", vData.stocks, aData.foils, vdIdx)
//      if (vdIdx < vendors.length && vData.stocks < 2 && aData.foils < 4)
//        this.createTally(vData, aData)
//
    } else if (aData.foils > 0) {
      let vIdx = Math.floor(Math.random() * aData.foils)
        , vId = aData.vendors[vIdx]
        , vData = vId ? this.agents.find(el=>(el.id == vId)) : null
      this.log.debug("  I:", aData.id, "; Pay a vendor", vIdx, 'of', aData.vendors.length, vId)
      if (vData) this.payVendor(aData, vIdx, vData)
    }
  }

// -----------------------------------------------------------------------------
  tryTally(aData, pDoc) {			//Try to request tally from someone in the world
    let requestTally = (aDat, pDat) => {
          let guidNS = uuidv5(aDat.peer_cid, uuidv5.DNS)
            , guid = uuidv5(pDoc.peer_cid, guidNS)
            , sig = "Valid"
            , contract = {name: "mychips-0.99"}
            , tallySql = "insert into mychips.tallies_v (tally_ent, tally_guid, partner, user_sig, contract, request) values ($1, $2, $3, $4, $5, $6);"
            , partner = 'test'

this.log.trace("Tally request:", tallySql)
          this.sqlDB.query(tallySql, [aDat.id, guid, pDat.id, sig, contract, 'draft'], (err,res) => {
            if (err) {this.log.error('In query:', err.stack); return}
            this.log.debug("  Initial tally by:", aDat.std_name, " with partner:", pDat.std_name)
            aDat.stocks++
//            pDat.foils++
          })
        }

this.log.debug("  Try tally:", aData.peer_cid, 'with', pDoc.peer_cid)
      this.checkPeer(pDoc, (pData, hadEm)=>{
        let host = pDoc.peer_sock.split(':')[0]
        if (hadEm)					//If we already had the peer in our array
          requestTally(aData, pData)			//Go ahead with the tally
        else this.docAc.insertOne({action: 'createUser', host, from:this.host, peer:aData}, ()=>{
this.log.debug("  Registering for callback:", pData.peer_cid, host)
          this.register(aData.peer_cid,host, ()=>{	//Else wait for the confirmation from the remote host
            requestTally(aData, pData)			//And then proceed
          })
        })
      })

    if (pDoc.host != this.host) {		//This person is on a different machine
    }


this.log.debug("  Request sent:", pDoc.peer_sock)
  }

// Check to see if a peer is in our system, if not add them and then do cb
// -----------------------------------------------------------------------------
  checkPeer(pData, cb) {			//Make sure we have a peer in our system
    let host, port
      , aData = this.agents.find(el=>(el.peer_cid == pData.peer_cid))
    if (pData.peer_sock) {[ host, port ] = pData.peer_sock.split(':')}		//If default socket, use it for host,port

this.log.debug("Checking if we have peer:", pData.peer_cid, !!aData)
    if (aData)
      cb(pData, true)
    else if (pData.host == this.host)
      this.log.error("Should have had local user:", pData.peer_cid)

    else this.sqlDB.query(peerSql, [pData.ent_name, pData.fir_name, pData.ent_type, pData.born_date, pData.peer_cid, pData.peer_host||host, pData.peer_port||port], (err,res) => {
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

    if (msg.state == 'peerProffer') {	//For now, we will just answer 'yes'
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
    let guidNS = uuidv5(vData.peer_cid, uuidv5.DNS)
      , guid = uuidv5(aData.peer_cid, guidNS)
      , sig = "Valid"
      , units = Math.floor(Math.random() * 100000)
      , seq = aData.foil_seqs[vIdx]			//Tally sequence
      , sql = "insert into mychips.chits_v (chit_ent,chit_seq,chit_guid,chit_type,signature,units) values ($1,$2,$3,'tran',$4,$5)"

this.log.debug("  payVendor:", aData.id, aData.foil_seqs, seq)
    this.sqlDB.query(sql, [aData.id,seq,guid,sig,units], (e,r) => {
      if (e) {this.log.error('In payment:', e.stack); return}
      this.log.debug("  payment:", aData.id, aData.std_name, "to:", vData.id, vData.std_name)
    })
  }

}		//class AgentCont

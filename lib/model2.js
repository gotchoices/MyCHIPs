//Version 2 agent-based model; Limited testing for distributed network
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
//-   When do I need more income?
//-   When do I want to buy more things?
//- 
const { dbClient } = require('wyseman')			//Connection to SQL
const Os = require('os')
const DocClient = require('mongodb').MongoClient	//Connection to doc DB
const MongoOpts = { useNewUrlParser: true, useUnifiedTopology: true }
const { Log } = require('wyclif')
const Uuid = require('uuid')
const parmQuery = "select parm,value from base.parm_v where module = 'model'"	//Operating parameters

const userSql = `select id, peer_cid, peer_agent,
    mychips.user_cert(id) as cert,
    stocks, foils, part_cids, vendors, clients,
    vendor_cids, vendor_agents, client_cids, stock_seqs, foil_seqs, net, types, seqs, targets
    from mychips.users_v_tallysum
    where not user_ent isnull`

// -----------------------------------------------------------------------------
module.exports = class {
  constructor(sqlConfig, docConfig, opts) {
    this.log = sqlConfig.log || Log('model-2')
    let dbConf = Object.assign({}, sqlConfig, {
      log: this.log,
      listen: ['parm_model', 'mychips_admin', 'mychips_user'],	//Asynchronous message from DB
    })
    let ddConf = Object.assign({}, {host: 'localhost', port: 27017, database: 'mychips'}, docConfig)

    if (!(this.agent = opts.agent)) {
      throw("Must supply and agent name")
    }
    this.log.info('Initializing agent-based model controller 2 for:', this.agent)
//console.log("opts:", opts)
    this.parms = {
      interval: opts.interval || 2000, 
      addclient: opts.client || 0.10,	//Try to add client 10% of the time
      checksets: 0.50,			//Try to adjust settings 50% of the time
      addvendor: opts.vendor || 0.40,	//Try to add vendors 15% of the time (not yet implemented)
      maxstocks: 2,
      maxfoils: 3,
      mintotpay: -10000,		//Make payments if net worth greater than this
      maxtopay: 0.10,			//Pay up to 10% of my net worth
      maxtarget: 100
    }
    this.entities = []

    this.entity = null		//Keep track of which user we are processing
    this.counter = 0
    if (opts.done) {this.doneCB = opts.done}		//Call on exit
    if (opts.runs) {this.runs = opts.runs}		//Max iterations

    this.sqlDB = new dbClient(dbConf, (channel, payload) => {	//Initialize Database connection
      let msg
      this.log.trace('Modeler DB async on:', channel, 'payload:', payload)
      if (payload) try {msg = JSON.parse(payload)} catch(e) {log.error("Parsing json payload: " + payload)}

      if (channel == 'parm_model') {				//Parameter updated
        this.log.debug("Parameter", msg.target, "=", msg.value, msg)
        if (msg.target in this.parms && msg.value) this.parms[msg.target] = msg.value

      } else if (channel == 'mychips_admin') {			//Something in the user data has changed
        if (msg.target == 'peers' || msg.target == 'tallies') {
          this.sqlDB.query(userSql + " and latest >= $1", [msg.time], (e,r)=>{this.eatEntities(e,r)})
        }

      } else if (channel == 'mychips_user') {			//Respond as a real user would to a request/event
        if (msg.target == 'tally') this.tallyState(msg)
      }
    })

    this.intervalTimer = null
    this.sqlDB.query(parmQuery, (e,r)=>{this.eatParms(e,r)})	//Load initial parameters
    
    let url = `mongodb://${ddConf.host}:${ddConf.port}`
    this.log.verbose("Mongo:", this.agent, url)
    this.docClient = new DocClient(url, MongoOpts)
    this.docClient.connect((err, client) => {			//Connect to mongodb
      if (err) {this.log.error('in Doc DB connect:', err.stack); return}
      this.docDB = client.db(ddConf.database)			//Pointer to DB connection

      this.docAg = this.docDB.collection("entities")	//Pointer to entities collection
//      this.docAg.createIndex({peer_cid: 1}, {unique: true})		//Should be multicolumn: cid, agent
//      this.docAg.countDocuments((e,r)=>{if (!e) this.worldPop = r})	//Actual people in doc DB
      this.log.trace("Connected to doc DB")
      this.sqlDB.query(userSql, (e,r)=>{this.eatEntities(e,r,true)})	//Load up initial set of users
    })
  }	//Constructor

// -----------------------------------------------------------------------------
  eatEntities(err, res, all) {					//Freshly load entity data from database
    if (err) {this.log.error('In query:', err.stack); return}
    if (!this.docDB) return					//Ingore until document db connected/ready
    this.log.trace('Loaded entities:', res.rows.length)
    let haveEm = []						//Keep track of which ones we've processed
//    console.log("eatEntities. Loaded:", res.rows.length)

    res.rows.forEach( row => {				//For each entity in sql result
      let aIdx = this.entities.findIndex(el=>(el.peer_cid == row.peer_cid))	//find him in my local list
      if (aIdx >= 0)					//Did we find him
        this.entities[aIdx] = row			//Replace his data in our list
      else
        this.entities.push(row)				//Or add him to our list

      haveEm.push(row.peer_cid)
      row.random = Math.random()			//Will help later in random selections
      row.agent = this.agent				//Mark user as belonging to us
      this.docAg.updateOne({peer_cid: row.peer_cid, agent: row.peer_agent}, {$set: row}, {upsert: true}, (e,r)=>{
        if (e) this.log.error(e.message)
        else this.log.trace("Add/update entity:", r)
      })
    })

    if (all) this.docAg.deleteMany({			//Delete any strays left in world db
      agent: this.agent,
      peer_cid: {$nin: haveEm}				//Those not in our recent batch get deleted
    }, (e,r) => {
      if (e) this.log.error(e.message)
      else this.log.debug("Delete entities in world:", r.n)
    })
    
    if (!this.entity && this.entities.length > 0) this.entity = 0	//Initialize loop to traverse entities
  }
  
// -----------------------------------------------------------------------------
  eatParms(err, res) {			//Digest updated operating parameters from database
    this.log.trace("eatParms")
    if (err) {this.log.error('In query:', err.stack); return}
    res.rows.forEach((row) => {
      let { parm, value } = row
      this.parms[parm] = value
    })
this.log.debug('Starting scheduler:', this.parms)
    if (this.intervalTimer) clearInterval(this.intervalTimer)	//Restart interval timer
    this.intervalTimer = setInterval(()=>{
      if (this.entity != null && (!this.runs || this.counter < this.runs)) {
        this.process(++this.counter)
      } else {
        this.close()
        if (this.doneCB) this.doneCB()
      }
    }, this.parms.interval)
  }
  
// -----------------------------------------------------------------------------
  close() {							//Shut down this simulation
    this.log.debug("Shutting down agent-based modeler")
    if (this.sqlDB.client.activeQuery) {			//If there is a query in process
      setTimeout(this.close, 500)				//Try again in a half second
    } else {
      this.sqlDB.disconnect()
    }
    this.docClient.close()
    if (this.intervalTimer) clearInterval(this.intervalTimer)
  }

// -----------------------------------------------------------------------------
  process(run) {						//Iterate on a single entity
    let aData = this.entities[this.entity]			//Point to entity's data
      , actSpace = Math.random()				//Randomize what action we will take

    this.log.verbose("Handler run:", run, this.entity, "/", this.entities.length, aData.id, aData.peer_cid)
    if (++this.entity >= this.entities.length) this.entity = 0	//Will go to next entity next time

this.log.debug("   stocks:", aData.stocks,'/', this.parms.maxstocks, "  max foils:", this.parms.maxfoils, "space:", actSpace)
    if (aData.stocks <= 0 || 			//I don't have any, or enough clients (or jobs)
       (actSpace < this.parms.addclient && aData.stocks < this.parms.maxstocks)) {
this.log.trace("    Searching for a client:")
      this.docAg.findOneAndUpdate({			//Look for a trading partner
        peer_cid: {
          $ne: aData.peer_cid,				//Don't find myself
          $nin: aData.part_cids				//Or anyone I'm already connected to
        },
//        agent: {$ne: this.agent},			//Look only on other sites
        foils: {$lte: this.parms.maxfoils},		//Or those with not too many foils already
      }, {
        $set: {random: Math.random()},			//re-randomize this person
        $inc: {foils: 1},				//And make it harder to get them again next time
        $push: {part_cids: aData.peer_cid}		//Immediately add ourselves to the array to avoid double connecting
      }, {						//Sort by
        sort: {foils: 1, random: -1}
      }, (e, res) => {					//Get result of query
        if (e) {
          this.log.error(e.errmsg)
        } else if (res.ok) {
this.log.verbose("  Best client:", res.value.peer_cid, res.value.agent, res.value.host)
          this.tryTally(aData, res.value)		//Try to start a tally with this entity
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
//      let vendors = this.entities.slice(0).sort((a,b)=>{return a.stocks - b.stocks})	//Sort potential vendors by how many vendors they have
//        , vdIdx = Math.floor(Math.random() * vendors.length / 4)			//Look in the first 25% of sort
//        , vData
//      for(vData = vendors[vdIdx]; vdIdx < vendors.length; vData = vendors[vdIdx++])
//        if (aData.id != vData.id && !aData.partners.includes(vData.id)) break		//Don't link to myself or the same person twice
//      this.log.debug("  attempt to ask:", vData.id, "to be my vendor", vData.stocks, aData.foils, vdIdx)
//      if (vdIdx < vendors.length && vData.stocks < 2 && aData.foils < 4)
//        this.createTally(vData, aData)

    } else if (aData.foils > 0 && aData.net > this.parms.mintotpay) {		//Time to make a payment
      let idx = Math.floor(Math.random() * aData.foils)
//        , vId = aData.vendors[idx]
//        , vData = vId ? this.entities.find(el=>(el.id == vId)) : null
      this.log.debug("  L:", aData.peer_cid, "pays vendor", idx, '/', aData.vendors.length, aData.vendor_cids[idx], "NW:", aData.net)
      this.payVendor(aData, idx)
    }
  }

// -----------------------------------------------------------------------------
  tryTally(aData, pDoc) {			//Try to request tally from someone in the world
this.log.trace("   Try tally:", aData.peer_cid, 'with', pDoc.peer_cid)
    let uuid = Uuid.v4()
      , sig = "Valid"
      , contract = {name: "mychips-0.99"}
      , tallySql = `insert into mychips.tallies_v (
          tally_ent, tally_uuid, contract, request, hold_cert, part_cert, hold_sig
        ) values ($1, $2, $3, $4, $5, $6, $7);`
      , parms = [aData.id, uuid, contract, 'offer', aData.cert, pDoc.cert, sig]

this.log.trace("  Tally request:", tallySql, parms)
    this.sqlDB.query(tallySql, parms, (err,res) => {
      if (err) {this.log.error('In query:', err.stack); return}
this.log.debug("   Initial tally by:", aData.peer_cid, " with:", pDoc.peer_cid)
      aData.stocks++
    })
  }

// -----------------------------------------------------------------------------
  tallyState(msg) {			//Someone is asking an entity to act on a tally
this.log.debug('Peer Message:', msg.state, msg.entity, msg.sequence)
    if (msg.state == 'P.offer') {		//For now, we will always answer 'yes'
this.log.verbose('  Tally offer for:', msg.entity, msg.sequence)
      let target = 1				//Immediately eligible for small lift
        , sql = `update mychips.tallies set request = 'open', hold_sig = $3, target = $4
          where tally_ent = $1 and tally_seq = $2 returning request, status;`
        , parms = [msg.entity, msg.sequence, 'Accepted', target]
      this.sqlDB.query(sql, parms, (e,r) => {
        if (e) {this.log.error('In :', e.stack); return}
        let row = r.rows && r.rows.length >= 1 ? r.rows[0] : null
//          , aData = this.entities.findIndex(el=>(el.peer_cid == row.peer_cid))
this.log.verbose('  Tally accepted:', row.tally_ent, row.tally_seq, row.request, '->', row.status)
      })
    }
  }

// -----------------------------------------------------------------------------
  payVendor(aData, idx) {
    let uuid = Uuid.v4()
      , sig = "Signed"							//Dummy signature
      , max = Math.max(aData.net * this.parms.maxtopay, 1000)		//Pay 1 CHIP or % of net worth
      , units = Math.floor(Math.random() * max)				//Random payment amount
      , seq = aData.foil_seqs[idx]					//Tally sequence
      , quid = 'Inv' + Math.floor(Math.random() * 1000)			//Invoice number
      , request = 'good'
      , sql = `insert into mychips.chits_v (
          chit_ent, chit_seq, chit_uuid, signature, units, memo, request
        ) values ($1, $2, $3, $4, $5, $6, $7)`
      , parms = [aData.id, seq, uuid, sig, units, quid, request]

this.log.verbose(" Vpay:", units, aData.peer_cid, "->", aData.vendor_cids[idx], aData.vendor_agents[idx], "on:", aData.id, seq)
    this.sqlDB.query(sql, parms, (e,r) => {
      if (e) {this.log.error('In payment:', e.stack); return}
      this.log.debug("  payment:", aData.peer_cid, "to:", aData.vendor_cids[idx], aData.vendor_agents[idx])
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

}		//class

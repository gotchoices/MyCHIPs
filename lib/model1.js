//Simple agent-based model; Works only locally on a single db instance
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// Parameters (opts):
// - runs: How many iterations to perform
// - interval: How many mSec beteween iterations
// - done: A function to call when finished
// - vendor: likelihood to try to add a vendor (0-1)
// - client: likelihood to try to add a client (0-1)
// TODO:
//- 
const { dbClient } = require('wyseman')
const { Log } = require('wyclif')
const Format = require('pg-format')
const Uuid = require('uuid')
const userFields = ['id', 'std_name', 'peer_cid']
const parmQuery = "select parm, value from base.parm_v where module = 'model'"
const userQuery = `select id, std_name, peer_cid, stocks, foils, part_cids, vendors, clients,
        mychips.user_cert(id) as cert
	from mychips.users_v_tallysum where not user_ent isnull`

module.exports = class {
  constructor(sqlConfig, junk, opts) {
    this.log = sqlConfig.log || Log('model-1')
    this.log.info('Initializing modeler controller')
    let dbConf = Object.assign({}, sqlConfig, {
      log: this.log,
      listen: ['parm_model', 'mychips_admin']
    })
    this.parms = {
      interval: opts.interval || 1000, 
      addclient: opts.client || 0.10, 
      addvendor: opts.vendor || 0.20
    }
    this.entities = []
    this.entity = null
    this.counter = 0
    if (opts.done) {this.doneCB = opts.done}			//Call on exit
    if (opts.runs) {this.runs = opts.runs}			//Max iterations

    this.log.debug('Connect to DB:', dbConf)
    this.db = new dbClient(dbConf, (channel, payload) => {	//Initialize Database connection
      var msg
      this.log.debug('Async message from DB:', channel, payload)
      if (payload) try {msg = JSON.parse(payload)} catch(e) {log.error("Parsing json payload: " + payload)}
      if (channel == 'parm_model') {
        this.log.debug("Parameter", msg.target, "=", msg.value, msg)
        if (msg.target in this.parms && msg.value) this.parms[msg.target] = msg.value
      
      } else if (channel == 'mychips_admin') {
//        this.log.debug("Async mychips_admin")
        this.db.query(userQuery, (e,r)=>{this.eatEntities(e,r)})
      }
    })
    this.intervalTimer = null
    this.db.query(parmQuery, (e,r)=>{this.eatParms(e,r)})
    this.db.query(userQuery, (e,r)=>{this.eatEntities(e,r)})
  }	//Constructor

  eatEntities(err, res) {				//Freshly load entity data from database
    if (err) {this.log.error('In query:', err.stack); return}
    this.entities = res.rows
    this.log.debug('Loaded entities:', res.rows.length)
    if (!this.entity && this.entities.length > 0) this.entity = 0
  }

  eatParms(err, res) {				//Digest operating parameters from database
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
  
  close() {							//Shut down this controller
    this.log.debug("Shutting down agent-based modeler")
    if (this.intervalTimer) clearInterval(this.intervalTimer)
    if (this.db.client.activeQuery) {				//If there is a query in process
      setTimeout(this.close, 500)				//Try again in a half second
    } else {
      this.db.disconnect()
    }
  }

  process() {						//Do transactions for a single entity
    let aData = this.entities[this.entity]
      , actSpace = Math.random()
    this.log.debug("Running entity handler", this.entity, "of", this.entities.length)
    this.log.debug("  Person:", aData.id, aData.std_name, 'S:', aData.stocks, 'F:', aData.foils)

    if (aData.stocks <= 0 || actSpace < this.parms.addclient) {				//I don't have any clients (or a job)
      let clients = this.entities.slice(0).sort((a,b)=>{return a.foils - b.foils})	//Sort potential clients by how many vendors they have
        , clIdx = Math.floor(Math.random() * clients.length / 4)			//Look in the first 25% of sort
        , cData
      for(cData = clients[clIdx]; clIdx < clients.length; cData = clients[clIdx++])
        if (aData.id != cData.id && !aData.part_cids.includes(cData.peer_cid)) break		//Don't link to myself or the same person twice
      this.log.debug("  attempt to ask:", cData.std_name, "to be my client", aData.stocks, cData.foils, clIdx)
      if (clIdx < clients.length && aData.stocks < 2 && cData.foils < 4)
        this.createTally(aData, cData)

    } else if (aData.foils <= 0 || actSpace < this.parms.addvendor) {			//I don't have any vendors, places to buy things
      let vendors = this.entities.slice(0).sort((a,b)=>{return a.stocks - b.stocks})	//Sort potential vendors by how many vendors they have
        , vdIdx = Math.floor(Math.random() * vendors.length / 4)			//Look in the first 25% of sort
        , vData
      for(vData = vendors[vdIdx]; vdIdx < vendors.length; vData = vendors[vdIdx++])
        if (aData.id != vData.id && !aData.part_cids.includes(vData.peer_cid)) break		//Don't link to myself or the same person twice
      this.log.debug("  attempt to ask:", vData.std_name, "to be my vendor", vData.stocks, aData.foils, vdIdx)
      if (vdIdx < vendors.length && vData.stocks < 2 && aData.foils < 4)
        this.createTally(vData, aData)

    } else if (aData.foils > 0) {
      let vIdx = Math.floor(Math.random() * aData.foils)
        , vId = aData.vendors[vIdx]
        , vData = vId ? this.entities.find(el=>(el.id == vId)) : null
      this.log.debug("  actSpace:", actSpace, "; Pay a vendor", vIdx, 'of', aData.vendors.length, vId)
this.log.debug("  a:", aData.foils, aData.vendors)
this.log.debug("  v:", vIdx, vId, vData)
      if (vData) this.payVendor(aData, vData)
    }

    if (++this.entity >= this.entities.length) this.entity = 0	//Go to next entity next time
  }

  mkUuid(cid, agent) {
    let url = 'chip://' + cid + ':' + agent
      , date = new Date().toISOString()
      , uuid = Uuid.v5(date, Uuid.v5(url, Uuid.v5.URL))
//console.log('date:', date, 'uuid:', uuid)
    return uuid
  }

  createTally(vData, cData) {					//We are not asking--just forcing (which would normally be illegal) an open tally into the DB
    let uuid = this.mkUuid(cData.peer_cid, cData.peer_agent)
      , sig = "Valid"
      , cont = '{"terms":"Our agreement"}'
      , sql = `insert into mychips.tallies (tally_type, status,
            tally_ent, tally_uuid, contract, part_ent, part_cert, hold_sig, part_sig
          ) values 
          ('stock','open', $1, $2, $3, $4, $5, $6, $7),
          ('foil' ,'open', $8, $9,$10,$11,$12,$13,$14) returning tally_seq;`
      , parms = [vData.id, uuid, cont, cData.id, cData.cert, sig, sig,
                 cData.id, uuid, cont, vData.id, vData.cert, sig, sig]
//this.log.debug("SQL:", sql, JSON.stringify(parms))
    this.db.query(sql, parms, (err,res) => {
      if (err) {this.log.error('In query:', err.stack); return}
      this.log.debug("  init tally vendor:", vData.std_name, "; client:", cData.std_name)
      vData.stocks++
      cData.foils++
    })
  }

  payVendor(aData, vData) {
    let uuid = this.mkUuid(aData.peer_cid, aData.peer_agent)
      , sig = "Valid"
      , units = Math.floor(Math.random() * 100000)
      , tSql = `select * from mychips.tallies where tally_ent = %L and
            status = 'open' and tally_type = %L and part_ent = %L order by crt_date desc limit 1`
      , tfSql = Format(tSql, aData.id, 'foil',  vData.id)
      , tsSql = Format(tSql, vData.id, 'stock', aData.id)
      , tvSql = Format("select %L::uuid as uuid, %L as sig, %s as units, 'good' as status", uuid, sig, units)
      , sql = `with tf as (${tfSql}), ts as (${tsSql}), tv as (${tvSql})
            insert into mychips.chits (chit_ent, chit_seq, chit_uuid, signature, units, status)
              select tf.tally_ent, tf.tally_seq, tv.uuid, tv.sig, tv.units, tv.status from tf,tv
            union 
              select ts.tally_ent, ts.tally_seq, tv.uuid, tv.sig, tv.units, tv.status from ts,tv;`
    this.log.debug("  payment:", aData.id, vData.id)
//this.log.debug("sql:", sql)
    this.db.query(sql, (err,res) => {
      if (err) {this.log.error('In query:', err.stack); return}
      this.log.debug("  payment:", aData.id, aData.std_name, "to:", vData.id, vData.std_name)
    })
  }

}		//class

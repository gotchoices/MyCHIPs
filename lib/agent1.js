//Simple agent-based model; Works only locally on a single db instance
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 
const { dbClient } = require('wyseman')
const { Log } = require('wyclif')
const uuidv5 = require('uuid/v5')
const userFields = ['id', 'std_name', 'peer_cid', 'serv_id']
const parmQuery = "select parm,value from base.parm_v where module = 'agent'"
const userQuery = `select id, std_name, peer_cid, stocks, foils, partners, vendors, clients
	from mychips.users_v_tallysum where not peer_ent isnull`

module.exports = class AgentCluster {
  constructor(sqlConfig, junk, argv) {
    this.log = Log('agent')
    this.log.info('Initializing agent model controller')
    let dbConf = Object.assign({
      log: this.log,
      listen: ['parm_agent', 'mychips_admin'],
    }, sqlConfig)
    this.parms = {interval: argv.interval || 1000, addclient: 0.10, addvendor: 0.20}
    this.agents = []
    this.agent = null
    this.counter = 0
    if (argv.runs) {this.runs = argv.runs}			//Max iterations
    this.db = new dbClient(dbConf, (channel, payload) => {	//Initialize Database connection
      var msg
      this.log.debug('Async agent message from DB:', channel, payload)
      if (payload) try {msg = JSON.parse(payload)} catch(e) {log.error("Parsing json payload: " + payload)}
      if (channel == 'parm_agent') {
        this.log.debug("Parameter", msg.target, "=", msg.value, msg)
        if (msg.target in this.parms && msg.value) this.parms[msg.target] = msg.value
      
//        if (msg.oper == 'UPDATE') this.db.query(parmQuery + " and mod_date >= $1", [msg.time], (e,r)=>{this.eatParms(e,r)})
      } else if (channel == 'mychips_admin') {
        this.db.query(userQuery, (e,r)=>{this.eatAgents(e,r)})
      }
    })
    this.intervalTimer = null
    this.db.query(parmQuery, (e,r)=>{this.eatParms(e,r)})
    this.db.query(userQuery, (e,r)=>{this.eatAgents(e,r)})
  }	//Constructor

  eatAgents(err, res) {						//Freshly load agent data from database
    if (err) {this.log.error('In query:', err.stack); return}
    this.agents = res.rows
    this.log.debug('Loaded agents:', res.rows.length)
    if (!this.agent && this.agents.length > 0) this.agent = 0
  }
  eatParms(err, res) {						//Digest operating parameters from database
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
  
  close() {							//Shut down this controller
    this.log.debug("Shutting down agent handler")
    if (this.db.client.activeQuery) {				//If there is a query in process
      setTimeout(this.close, 500)				//Try again in a half second
    } else {
      this.db.disconnect()
    }
    if (this.intervalTimer) clearInterval(this.intervalTimer)
  }

  process() {							//Iterate on a single agent
    let aData = this.agents[this.agent]
      , actSpace = Math.random()
    this.log.debug("Running agent handler", this.agent, "of", this.agents.length)
    this.log.debug("  Person:", aData.id, aData.std_name)

    if (aData.stocks <= 0 || actSpace < this.parms.addclient) {				//I don't have any clients (or a job)
      let clients = this.agents.slice(0).sort((a,b)=>{return a.foils - b.foils})	//Sort potential clients by how many vendors they have
        , clIdx = Math.floor(Math.random() * clients.length / 4)			//Look in the first 25% of sort
        , cData
      for(cData = clients[clIdx]; clIdx < clients.length; cData = clients[clIdx++])
        if (aData.id != cData.id && !aData.partners.includes(cData.id)) break		//Don't link to myself or the same person twice
      this.log.debug("  attempt to ask:", cData.std_name, "to be my client", aData.stocks, cData.foils, clIdx)
      if (clIdx < clients.length && aData.stocks < 2 && cData.foils < 4)
        this.createTally(aData, cData)

    } else if (aData.foils <= 0 || actSpace < this.parms.addvendor) {			//I don't have any vendors, places to buy things
      let vendors = this.agents.slice(0).sort((a,b)=>{return a.stocks - b.stocks})	//Sort potential vendors by how many vendors they have
        , vdIdx = Math.floor(Math.random() * vendors.length / 4)			//Look in the first 25% of sort
        , vData
      for(vData = vendors[vdIdx]; vdIdx < vendors.length; vData = vendors[vdIdx++])
        if (aData.id != vData.id && !aData.partners.includes(vData.id)) break		//Don't link to myself or the same person twice
      this.log.debug("  attempt to ask:", vData.std_name, "to be my vendor", vData.stocks, aData.foils, vdIdx)
      if (vdIdx < vendors.length && vData.stocks < 2 && aData.foils < 4)
        this.createTally(vData, aData)

    } else if (aData.foils > 0) {
      let vIdx = Math.floor(Math.random() * aData.foils)
        , vId = aData.vendors[vIdx]
        , vData = vId ? this.agents.find(el=>(el.id == vId)) : null
      this.log.debug("  actSpace:", actSpace, "; Pay a vendor", vIdx, 'of', aData.vendors.length, vId)
      if (vData) this.payVendor(aData, vData)
    }

    if (++this.agent >= this.agents.length) this.agent = 0	//Go to next agent next time
  }

  createTally(vData, cData) {					//We are not asking--just forcing (which would normally be illegal) an open tally into the DB
    let uuidNS = uuidv5(vData.peer_cid, uuidv5.DNS)
      , uuid = uuidv5(cData.peer_cid, uuidNS)
      , sig = "Valid"
      , sql = `insert into mychips.tallies (tally_ent,partner,tally_uuid,tally_type,status,hold_sig,part_sig) values 
          ($1,$2,$3,'stock','open',$4,$5),
          ($6,$7,$8,'foil' ,'open',$9,$10) returning tally_seq;`
    this.db.query(sql, [vData.id,cData.id,uuid,sig,sig,cData.id,vData.id,uuid,sig,sig], (err,res) => {
      if (err) {this.log.error('In query:', err.stack); return}
      this.log.debug("  init tally vendor:", vData.std_name, "; client:", cData.std_name)
      vData.stocks++
      cData.foils++
    })
  }

  payVendor(aData, vData) {
    let uuidNS = uuidv5(vData.peer_cid, uuidv5.DNS)
      , uuid = uuidv5(aData.peer_cid, uuidNS)
      , sig = "Valid"
      , units = Math.floor(Math.random() * 100000)
      , sql = `insert into mychips.chits (chit_ent,chit_seq,chit_uuid,chit_type,signature,units,status) values 
          ($1,mychips.tally_find($1,$5,'foil'),$2,'tran',$3,$4,'good'),
          ($5,mychips.tally_find($5,$1,'stock'),$6,'tran',$7,$8,'good') returning chit_seq;`
    this.log.debug("  payment:", aData.id, vData.id)
    this.db.query(sql, [aData.id,uuid,sig,units,vData.id,uuid,sig,units], (err,res) => {
      if (err) {this.log.error('In query:', err.stack); return}
      this.log.debug("  payment:", aData.id, aData.std_name, "to:", vData.id, vData.std_name)
    })
  }

}		//class AgentCont

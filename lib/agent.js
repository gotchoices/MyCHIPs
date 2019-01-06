//Agent-based model
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- Read initial parameters from base.parm_v
//- Establish interrupt schedule
//- On each cycle, call an actor function on behalf of each entity
//- Make decisions like:
//-   Establishing new tallies (stock and foil)
//-   Closing old tallies?
//-   Paying people down-stream of me
//-   Establishing buy/sell orders
//- 
//- How to specify the database we want to connect to (for this and all modules)
//- 
const { dbClient } = require('wyseman')
const uuidv5 = require('uuid/v5')
const userFields = ['id', 'std_name', 'peer_cdi', 'host_id']
const parmQuery = "select parm,value from base.parm_v where module = 'agent'"
const userQuery = `select id, std_name, peer_cdi,
	coalesce(s.stocks,0) as stocks, coalesce(s.foils,0) as foils,
	coalesce(s.partners,'{}'::int[]) as partners,
	coalesce(s.vendors,'{}'::int[]) as vendors,
	coalesce(s.clients,'{}'::int[]) as clients
	from		mychips.users_v u
	left join	mychips.tallies_v_sum s on s.tally_ent = u.id where id >= 100 order by id`

module.exports = class AgentCluster {
  constructor(config) {
    this.log = require('./logger')('agent')
    this.log.info('Initializing agent model controller')
    let dbConf = {
      logger: this.log,
      listen: ['mychips_agent', 'mychips_admin'],
    }
    this.parms = {interval: 1000, addclient: 0.10, addvendor: 0.20}
    this.agents = []
    this.agent = null
    Object.assign(dbConf, config)				//Merge in any user specified database arguments
    this.db = new dbClient(dbConf, (channel, payload) => {	//Initialize Database connection
      this.log.debug('Async agent message from DB:', channel, payload)
      var msg = JSON.parse(payload)
      if (channel == 'mychips_agent') {
        if (msg.oper == 'UPDATE') this.db.query(parmQuery + " and mod_date >= $1", [msg.time], (e,r)=>{this.eatParms(e,r)})
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
      if (this.agent != null) this.process()
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
    let guidNS = uuidv5(vData.peer_cdi, uuidv5.DNS)
      , guid = uuidv5(cData.peer_cdi, guidNS)
      , sig = "Valid"
      , sql = `insert into mychips.tallies (tally_ent,partner,tally_guid,tally_type,status,user_sig,part_sig) values 
          ($1,$2,$3,'stock','open',$4,$5),
          ($6,$7,$8,'foil' ,'open',$9,$10) returning tally_seq;`
    this.db.query(sql, [vData.id,cData.id,guid,sig,sig,cData.id,vData.id,guid,sig,sig], (err,res) => {
      if (err) {this.log.error('In query:', err.stack); return}
      this.log.debug("  init tally vendor:", vData.std_name, "; client:", cData.std_name)
      vData.stocks++
      cData.foils++
    })
  }

  payVendor(aData, vData) {
    let guidNS = uuidv5(vData.peer_cdi, uuidv5.DNS)
      , guid = uuidv5(aData.peer_cdi, guidNS)
      , sig = "Valid"
      , units = Math.floor(Math.random() * 100000)
      , sql = `insert into mychips.chits (chit_ent,chit_seq,chit_guid,chit_type,signature,units) values 
          ($1,mychips.tally_find($1,$5,'foil'),$2,'tran',$3,$4),
          ($5,mychips.tally_find($5,$1,'stock'),$6,'tran',$7,$8) returning chit_seq;`
    this.log.debug("  payment:", aData.id, vData.id)
    this.db.query(sql, [aData.id,guid,sig,units,vData.id,guid,sig,units], (err,res) => {
      if (err) {this.log.error('In query:', err.stack); return}
      this.log.debug("  payment:", aData.id, aData.std_name, "to:", vData.id, vData.std_name)
    })
  }

}		//class AgentCont

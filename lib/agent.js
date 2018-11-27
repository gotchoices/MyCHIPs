//Agent-based model
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// Open a socket on a specified port to listen for connections from other peers.
// Also initiate various actions with other peers on appropriate asynchronous 
// triggers coming from the database.
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
const userQuery = "select id,std_name,peer_cdi,coalesce(stocks,0) as stocks, coalesce(foils,0) as foils from mychips.users_v u left join mychips.tallies_v_sum s on s.tally_ent = u.id where id >= 100 order by id"
const parmQuery = "select parm,value from base.parm_v where module = 'agent'"

module.exports = class AgentCont {
  constructor(config) {
    this.log = require('./logger')('agent')
    this.log.info('Initializing agent model controller')
    let dbConf = {
      logger: this.log,
      listen: ['mychips_agent', 'mychips_admin'],
      schema: __dirname + "/schema.sql"
    }
    this.parms = {interval: 1000}
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
    if (!this.agent && this.agents.length > 0) this.agent = 0
  }
  eatParms(err, res) {						//Digest operating parameters from database
    if (err) {this.log.error('In query:', err.stack); return}
    res.rows.forEach((row) => {
      let { parm, value } = row
      this.parms[parm] = value
    })

    if (this.intervalTimer) clearInterval(this.intervalTimer)	//Restart interval timer
    this.intervalTimer = setInterval(()=>{this.process()}, this.parms.interval)
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
    this.log.debug("  Name:", aData.std_name)

    if (aData.stocks <= 0) {					//I don't have any clients (or a job)
      let clients = this.agents.slice(0).sort((a,b)=>{return a.foils - b.foils})	//Sort potential clients by how many vendors they have
        , clData = (aData.id == clients[0].id) ? clients[1] : clients[0]	//Find someone besides me, to ask to be my vendor
      this.log.debug("  will ask:", clData.std_name, "to be my client")
      this.createTally(aData, clData)
    } else if (actSpace < 0.10) {
      let clIndex = Math.floor(Math.random() * this.agents.length)
        , clData = aData[clIndex]
      this.log.debug("  actSpace:", actSpace, "; Consider another client:", clIndex, clData)
      if (aData.stocks < 3 && clData && clData.foils < 3)
        this.createTally(aData, clData)
    } else if (actSpace < 0.20) {
      this.log.debug("  actSpace:", actSpace, "; Look for new vendors?")
    } else {
      this.log.debug("  actSpace:", actSpace, "; Pay a vendor")
      this.payVendor(aData)
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

  payVendor(aData) {
//    let guidNS = uuidv5(vData.peer_cdi, uuidv5.DNS)
//      , guid = uuidv5(cData.peer_cdi, guidNS)
//      , sig = "Valid"
//      , sql = `insert into mychips.tallies (tally_ent,partner,tally_guid,tally_type,status,user_sig,part_sig) values 
//          ($1,$2,'$3','stock','open',$4,$5),
//          ($6,$7,'$8','foil' ,'open',$9,$10) returning tally_seq;`
//    this.db.query(sql, [vData.id,cData.id,guid,sig,sig,cData.id,vData.id,guid,sig,sig], (err,res) => {
//      if (err) {this.log.error('In query:', err.stack); return}
//      this.log.debug("  init tally vendor:", vData.std_name, "; client:", cData.std_name)
//      vData.stocks++
//      cData.foils++
//    })
  }

}		//class AgentCont

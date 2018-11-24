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

module.exports = class AgentCont {
  constructor(config) {
    this.log = require('./logger')('agent')
    this.log.info('Initializing agent model controller')
    let dbConf = {
      logger: this.log,
      listen: 'mychips_agent',
      schema: __dirname + "/schema.sql"
    }
    this.parms = {interval: 1000}
    Object.assign(dbConf, config)				//Merge in any user specified database arguments
    this.db = new dbClient(dbConf, (channel, payload) => {	//Initialize Database connection
      this.log.debug('Async agent message from DB:', channel, payload)
      var msg = JSON.parse(payload)
      if (msg.oper == 'UPDATE') this.db.query("select parm,value from base.parm_v where module = 'agent' and mod_date >= $1", [msg.time], (e,r)=>{this.eatParms(e,r)})
    })
    this.intervalTimer = null
    this.db.query("select base.parm_int('agent','interval')", (e,r)=>{this.eatParms(e,r)})
  }	//Constructor

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
    this.log.debug("Running agent handler")
  }

}		//class AgentCont

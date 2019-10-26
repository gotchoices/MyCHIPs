//Lift Scheduler
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// This calls on the database to initiate lifts on a configurable schedule
// TODO:
//X- Settable lift interval DB parameter
//X- Automatically detect changes to the parameter
//X- Keep a timeout interval running
//X- Call the DB to initiate lifts on that schedule
//- Make an .ini file to populate/document base.parms with our module parameters
//- 
const { dbClient } = require('wyseman')
const { Log } = require('wyclif')
const parmQuery = "select parm,value from base.parm_v where module = 'lifts'"

module.exports = class LiftScheduler {
  constructor(config) {
    let dbConf = {
      log: this.log,
      listen: ['parm_lifts'],
    }
    this.log = Log('lifts')
    this.log.info('Initializing lift scheduling controller')

    this.parms = {interval: 1000, limit:1}
    if (config) Object.keys(this.parms).forEach(key=>{
      if (key in config) this.parms[key] = config[key]
    })

    this.db = new dbClient(dbConf, (channel, payload) => {	//Initialize Database connection
      this.log.debug('Async lifts message from DB:', channel, payload)
      let msg
      if (payload) try {msg = JSON.parse(payload)} catch(e) {log.error("Parsing json payload: " + payload)}
#Fixme: just grab parameter value from payload now
#      if (msg.oper == 'UPDATE') this.db.query(parmQuery + " and mod_date >= $1", [msg.time], (e,r)=>{
#        this.eatParms(e,r)
#      })
    })

    this.intervalTimer = null
    this.db.query(parmQuery, (e,r)=>{this.eatParms(e,r)})
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
    this.log.debug("Shutting down lift handler")
    if (this.db.client.activeQuery) {				//If there is a query in process
      setTimeout(this.close, 500)				//Try again in a half second
    } else {
      this.db.disconnect()
    }
    if (this.intervalTimer) clearInterval(this.intervalTimer)
  }

  process() {						//Iterate on a single agent
    this.log.debug("Running lift handler")
    let sql = 'select mychips.lift_cycle($1);'
    this.db.query(sql, [this.parms.limit], (err,res) => {
      if (err) {this.log.error('In lift function:', err.stack); return}
      this.log.debug("  Lift results:", res)
    })
  }

}		//class LiftScheduler

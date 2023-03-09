//Master Scheduler
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// There should be exactly one instance of this module running for each DB instance.
// TODO:
//- Convert to modular schedular
//- Can handle lift requests
//- Can handle exchange queries
//- 
const { dbClient } = require('wyseman')
const { Log } = require('wyclif')
const parmQuery = "select parm,value from base.parm_v where module = $1"

module.exports = class Scheduler {
  constructor(config = {}) {
    let control = {
      lifts: {
        parms: {interval: 30000, limit: 1},
        handler: () => this.liftsHandler()
      },
      exchange: {
        parms: {interval: 43200, limit: 1},
        handler: () => this.exchangeHandler(),
        onStart: true
      }
    }
      , modules = Object.keys(control)
      , listen = modules.map(k => ('parm_' + k))
      , log = Log('scheduler')
      , dbConf = Object.assign({log, listen}, config.db)

    this.log = log
    this.control = control
    this.modules = modules
    this.log.info('Initializing scheduler modules: ', modules.join(','))

    this.db = new dbClient(dbConf, (channel, payload) => {	//Initialize Database connection
this.log.debug('Async from DB:', channel, payload)
      let msg
      if (payload) try {msg = JSON.parse(payload)} catch(e) {log.error("Parsing json payload: " + payload)}
      if (modules.indexOf(msg.target) >= 0) {	//Found parm for one of our modules
        let cont = control[msg.target]
this.log.debug("Parameter:", msg.target, ':', msg.parm, "=", msg.value, msg)
        if (msg.parm in cont.parms && msg.value)
          cont.parms[msg.parm] = msg.value
        if (msg.parm == 'interval')
          this.restart(msg.target)
      }
    })

    modules.forEach(module => {
      let conf = config[module]
        , cont = this.control[module]
      if (conf) Object.keys(cont.parms).forEach(parm => {
        if (parm in conf) cont.parms[parm] = conf[parm]
      })

      this.db.query(parmQuery, [module], (err, res) => {
        if (err) this.log.error('In query:', err.stack)
this.log.debug("Query rows:", res?.rows)

        res?.rows.forEach((row) => {
          let { parm, value } = row
this.log.debug("Scheduler set", module, ':', parm, '=', value)
          cont.parms[parm] = value
        })
        this.restart(module)
      })
    })
  }	//Constructor

  restart(module) {			//Set interrupt schedule for this module
    let cont = this.control[module]
this.log.debug("Scheduler setting interval:", module, cont.parms.interval)
    if (cont.intervalTimer)
      clearInterval(cont.intervalTimer)
    cont.intervalTimer = setInterval(()=>{
this.log.debug("H:", module, cont)
    cont.handler()
    }, cont.parms.interval)
  }
  
  close() {							//Shut down this instance
    this.log.debug("Shutting down lift handler")
    if (this.db.client.activeQuery) {				//If there is a query in process
      setTimeout(this.close, 500)				//Try again in a half second
    } else {
      this.db.disconnect()
    }
    this.modules.forEach(module => {
      let cont = this.control[module]
      if (cont.intervalTimer)
        clearInterval(cont.intervalTimer)
    })
  }

  liftsHandler() {				//Initiate a lift check
    let lifts = this.control.lifts
this.log.debug("Running lift check")
    let sql = 'select mychips.lift_cycle($1);'
    this.db.query(sql, [lifts.parms.limit], (err, res) => {
      if (err) {this.log.error('In lift function:', err.stack); return}
      this.log.debug("  Lift results:", res)
    })
  }

  exchangeHandler() {				//Do we have exchange data for today
    let exchange = this.control.exchange
this.log.debug("Running exchange check")
    let sql = 'select * from base.exchange where sample = current_date;'
    this.db.query(sql, (err, res) => {
      if (err) {this.log.error('Querying exchange rates:', err.stack); return}
      this.log.debug("  Lift results:", res)
this.log.debug("fetch:", global?.fetch)
    })
  }

}		//class Scheduler

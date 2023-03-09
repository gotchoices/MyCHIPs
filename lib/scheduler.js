//Master Scheduler
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// There should be exactly one instance of this module running for each DB instance.
const { dbClient } = require('wyseman')
const { Log } = require('wyclif')
const Fetch = require('node-fetch')
const exchangeURL = "https://api.exchangerate-api.com/v4/latest/USD"
const parmQuery = "select parm,value from base.parm_v where module = $1"
const checkSql = 'select count(*) from base.exchange where sample = current_date;'

//Join exchange data with currencies DB, insert rates only for known codes
const exchSql = `
  with ex as (select * from jsonb_each($1))
  insert into base.exchange (curr, rate, sample)
    select c.cur_code, ex.value::numeric as rate, $2
      from ex
      join base.currency c on c.cur_code = ex.key
      where ex.key != 'USD'
  on conflict on constraint exchange_pkey do update set rate = EXCLUDED.rate;`

module.exports = class Scheduler {
  constructor(config = {}) {
    let control = {
      lifts: {
        parms: {interval: 5 * 60 * 1000, limit: 1},
        handler: c => this.liftsHandler(c)
      },
      exchange: {
        parms: {interval: 12 * 60 * 60 * 1000, limit: 1},
        handler: c => this.exchangeHandler(c),
        onStart: true
      }
    }
      , modules = Object.keys(control)			//Array of module names
      , listen = modules.map(k => ('parm_' + k))	//Tags we listen for DB Async on
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
    }, () => this.init())			//Call init after DB connected

    this.modules.forEach(module => {		//Establish any passed configuation defaults
      let conf = config[module]
        , cont = this.control[module]
      if (conf) Object.keys(cont.parms).forEach(parm => {
        if (parm in conf) cont.parms[parm] = conf[parm]
      })
    })
  }	//Constructor

  init() {					//Initialize all modules
    this.modules.forEach(module => {
      let cont = this.control[module]

      this.db.query(parmQuery, [module], (err, res) => {	//Query db for settings
        if (err) this.log.error('In query:', err.stack)

        res?.rows.forEach((row) => {
          let { parm, value } = row
this.log.trace("Scheduler set", module, ':', parm, '=', value)
          cont.parms[parm] = value
        })
        this.restart(module)
      })
      if (cont.onStart) cont.handler(cont)	//Do initial run on start
    })
  }	//Init

  restart(module) {			//Set interrupt schedule for this module
    let cont = this.control[module]
//this.log.debug("Scheduler setting interval:", module, cont.parms.interval)
    if (cont.intervalTimer)
      clearInterval(cont.intervalTimer)
    cont.intervalTimer = setInterval(()=>{
      cont.handler(cont)
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

  liftsHandler(cont) {				//Initiate a lift check
this.log.debug("Running lift check")
    let sql = 'select mychips.lift_local($1);'
    this.db.query(sql, [cont.parms.limit], (err, res) => {
      if (err) {this.log.error('In lift function:', err.stack); return}
//this.log.debug("  Lift results:", res)
    })
  }

  exchangeHandler(cont) {			//Do we have exchange data for today
this.log.debug("Running exchange check")
    this.db.query(checkSql).then(res => {	//;this.log.debug("  DB check results:", res)
      let row = res?.rows[0] ?? {}
      if (row.count > 0) throw 'Existing data found'
      return Fetch(exchangeURL)
    }).then(res => {
      return res.json()

    }).then(res => {				//;this.log.debug("  Exchange results:", res)
      let rates = res?.rates
      if (res?.base != 'USD' || !rates) throw 'Exchange record not found'
      if (rates.USD != 1) throw 'Exchange not default USD based'
      return this.db.query(exchSql, [rates, res.date])

    }).then(res => {				//;this.log.debug("  Insert results:", res)
      if (res?.rowCount <= 100) throw 'Exchange insert failed'
    }).catch(err => {
      this.log.error('Querying exchange rates:', err)
    })
  }

}		//class Scheduler

//Master Scheduler
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// There should be exactly one instance of this module running for each DB instance.
const { dbClient } = require('wyseman')
const { Log } = require('wyclif')
const Fetch = require('node-fetch')
const Cron = require('node-cron')
const exchangeURL = "https://open.er-api.com/v6/latest/USD"
const parmQuery = "select parm,value from base.parm_v where module = $1"
const checkXchSql = "select count(*) from base.exchange where sample = current_date;"
const symbCHIP = 'XCH'
const checkCHIPSql = `select * from base.exchange where curr = '${symbCHIP}' order by sample desc limit 1;`
const chipURL = "https://mychips.org/chip-latest.json"
const Minute = 60
const Hour = Minute * 60
const Day = Hour * 24

//Join exchange data with currencies DB, insert rates only for known codes
const exchSql = `with ex as (select * from jsonb_each($1))
  insert into base.exchange (curr, rate, sample)
    select c.cur_code, ex.value::numeric as rate, $2
      from ex
      join base.currency c on c.cur_code = ex.key
  on conflict on constraint exchange_pkey do update set rate = EXCLUDED.rate;`

module.exports = class Scheduler {
  constructor(config = {}) {
    let control = {		//Make control structure for each module
      lifts: {
        parms: {interval: 5 * Minute, limit: 1},
        handler: c => this.liftsHandler(c)
      },
      exchange: {
        parms: {interval: '0 12 * * *'},
        handler: c => this.exchangeHandler(c),
        onStart: true
      },
      chip: {
        parms: {interval: '* * 12 16 * *'},
        handler: c => this.chipHandler(c),
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
    }, () => this.init())			//Finish initializing after DB connected

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
this.log.trace("Scheduler init:", module)
      this.db.query(parmQuery, [module], (err, res) => {	//Query db for settings
        if (err) this.log.error('In query:', err.stack)

        res?.rows.forEach((row) => {
          let { parm, value } = row
this.log.trace("Scheduler set", module, ':', parm, '=', value)
          cont.parms[parm] = value
        })
        this.restart(module)
      })
      if (cont.onStart) cont.handler(cont)		//Do initial run on start
    })
  }	//Init

  clear(cont) {				//Stop any pending job for this module
    if (cont.intervalTimer)
      clearInterval(cont.intervalTimer)
    if (cont.cronJob) {
      cont.cronJob.stop()
      delete cont.cronJob
    }
  }
  
  restart(module) {			//Set interrupt schedule for this module
    let cont = this.control[module]
      , interval = cont.parms.interval
    this.clear(cont)

    if (typeof interval === 'string' && Cron.validate(interval)) {	//Interval in cron format
this.log.debug("Setting:", module, "cron:", interval)
      cont.cronJob = Cron.schedule(interval, () => cont.handler(cont))

    } else if (/^\d+$/.test(interval)) {			//Interval given in seconds
this.log.debug("Setting interval:", module, interval)
      cont.intervalTimer = setInterval(()=>{
        cont.handler(cont)
      }, cont.parms.interval * 1000)

    } else {
      this.log.error("Bad interval format:", interval, 'module:',  module)
    }
  }
  
  close() {						//Shut down this instance
    this.log.debug("Shutting down lift handler")
    if (this.db.client.activeQuery) {			//If there is a query in process
      setTimeout(this.close, 500)			//Try again in a bit
    } else {
      this.db.disconnect()
    }
    this.modules.forEach(module => {
      let cont = this.control[module]
      this.clear(cont)
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

  chipHandler(cont) {		//Grab latest chip value estimation
this.log.debug("CHIP Value Handler:", cont)
    this.db.query(checkCHIPSql).then(res => {
      let row = res?.rows[0] ?? {}
        , today = new Date()				;this.log.debug("  DB CHIP sample:", row)
      if (row.sample && row.sample >= today) return
      Fetch(chipURL).then(res => res.json()).then(res => {	this.log.debug('chip:', res)
        let { date, base, value } = res
          , sql = 'insert into base.exchange (curr, base, rate, sample) values ($1, $2, $3, $4);'
        return(this.db.query(sql, [symbCHIP, base, value, date]))
//      }).then(res => {				this.log.debug('wres:', res)
      }).catch(err => {
      this.log.error("Setting CHIP exchange rate:", err)
      })
    })
  }

  exchangeHandler(cont) {			//Do we have exchange data for today
this.log.debug("Running exchange check:", exchangeURL)
    this.db.query(checkXchSql).then(res => {
      let row = res?.rows[0] ?? {}			//;this.log.debug("  DB xch results:", row)
      if (row.count > 0) throw 'Existing data found'	//;this.log.debug("  Fetching:", exchangeURL)
      return Fetch(exchangeURL)
    }).then(res => {
      return res.json()

    }).then(res => {				//;this.log.debug("  Exchange results:", res)
      let rates = res?.rates
        , sample = new Date(res?.time_last_update_utc)
this.log.debug("Exchange date:", sample)
      if (res?.base_code != 'USD' || !rates || res?.result != 'success')
        throw 'Exchange record not found'
      if (rates.USD != 1) throw 'Exchange not default USD based'
      return this.db.query(exchSql, [rates, sample])

    }).then(res => {				//;this.log.debug("  Insert results:", res)
      if (res?.rowCount <= 100) throw 'Exchange insert failed'
    }).catch(err => {
      this.log.error('Querying exchange rates:', err)
    })
  }

}		//class Scheduler

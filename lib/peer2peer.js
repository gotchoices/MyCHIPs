//Peer to peer user-agent controller
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// Open a socket on a specified port to listen for connections from other peers.
// Also initiate various actions with other peers on appropriate asynchronous 
// triggers coming from the database.
// -----------------------------------------------------------------------------
// TODO:
//X- Implement state processor for lifts
//X- Leave connections open until they time out
//- Check for unreasonably large messages?
//- Seam in noise protocol driver
//- DH key passed in from main, used in noise
//- 
const Os = require('os')
const Crypto = require('crypto')
const Format = require('pg-format')
const { dbClient } = require('wyseman')
const { Log } = require('wyclif')
const Net = require('net')
const Tally = require('./tally')
const Chit = require('./chit')
const Route = require('./route')
const Lift = require('./lift')
const PeerNoise = require('./peernoise.js')
const parmQuery = "select parm,value from base.parm_v where module = 'peers'"
const LongPoll = 3600000			//60 min
const ShortPoll = 60000				//60 sec
const MinTime = 5
const MaxTries = 4

module.exports = class PeerCont {
  constructor(servConfig, dbConfig) {
    let { host, port, keys } = servConfig
      , agent = servConfig.agent || Buffer.from(keys.publicKey).toString('base64url')
      , log = this.log = servConfig.log || Log('agent' + (agent ? '_' + agent.slice(-4) : ''))
      , dbConf = {
          log,
          listen: ['parm_peers', (agent ? 'ma_' + agent : 'mychips_agent')],
        }	
    Object.keys(dbConfig).forEach(k => dbConf[k] ||= dbConfig[k])	//Merge in any user specified database arguments
    this.parms = {minTime: MinTime, maxTries: MaxTries}	//In minutes
    this.pollTime = ShortPoll				//In msec

    this.log.info('Initializing peer server at:', host, port, 'Agent:', keys)

    this.peerNoise = new PeerNoise({
      host, port, keys, log, 
      queryCB:(r,d,c)=>this.query(r,d,c)
    }, (serv, msg) => {
      this.log.debug('Incoming message from peer:', serv.peerAgent, 'Msg:', msg)
      if (msg.target in this.targets) {			//If we have a handler for the specified target (tally, chit, etc.)
        let target = this.targets[msg.target]
        this.log.verbose('Remote async:', msg.target, msg.action, msg.object)
        if (msg.action in target.remote) {
          if (this.failReceive) {				//For regression testing only
            let mSec = parseInt(this.failReceive)
            if (mSec) setTimeout(()=>{
              target.remote[msg.action].call(this, msg, serv)	//Call state handler after a simulated network delay
            }, mSec)
          } else {
            target.remote[msg.action].call(this, msg, serv)	//Call state handler
          }
        }
      }
    })
    
    this.db = new dbClient(dbConf, (channel, payload) => {	//Initialize Database connection
      this.log.trace('Peer DB async on:', channel, payload)
      let msg
      if (payload) try {msg = JSON.parse(payload)} catch(e) {log.error("Parsing json payload: " + payload)}
      if (channel == 'parm_peers') {
        this.log.verbose("Parameter", msg.target, "=", msg.value, msg)
        if (msg.target in this.parms && msg.value) {
          this.parms[msg.target] = msg.value
          this.poll()
        }

      } else if (msg && msg.target in this.targets) {		//If we have a handler for the specified target (tally, chit, etc.)
        let target = this.targets[msg.target]
        this.log.verbose('DB async:', channel, msg.target, msg.action)
        if (msg.action in target.local)
          target.local[msg.action].call(this, msg)		//Call state handler
      }
      this.pollTime = ShortPoll					//Poll again quickly
    })
    
    this.closeDB=false
    this.targets = {}
    this.targets.tally = Tally
    this.targets.chit = Chit
    this.targets.route = Route
    this.targets.lift = Lift

    this.pollTimer = null
    this.db.query(parmQuery, (e,r)=>{
      if (e) {this.log.error('Getting peers parameters:', e.message); return}
this.log.debug('Peer got parms:', r.rows.length)
      r.rows.forEach(row => {
        let { parm, value } = row
        this.parms[parm] = value
      })
      if (servConfig.poll === 'undefined' || servConfig.poll) this.poll()
    })
  }	//Constructor
  
  poll(t) {						//Ask the database for any stale traffic
    this.pollTime = t || LongPoll
    this.db.query("select mychips.tally_notices()", (e,r)=>{
      if (e) {this.log.error('Polling database:', e.message); return}
this.log.trace("Poll request complete:")      //Real results will come asynchronously
    })

this.log.debug("Peer server polling:", this.pollTime, t, new Date())
    if (this.pollTimer) clearTimeout(this.pollTimer)	//Restart timer
    this.pollTimer = setTimeout(()=>{this.poll()}, this.pollTime)
  }

  close() {							//Shut down this controller
    this.peerNoise.close()
//this.log.debug("Polling status:", this.pollTimer)
    if (this.pollTimer) clearTimeout(this.pollTimer)

//this.log.debug("DB status:", this.db.client.activeQuery)
    if (this.db.client.activeQuery) {				//Is there a query in process?
      this.closeDB = true
    } else {
      this.db.disconnect()
    }
  }
  
  peerError(msg, err) {
    let ctxMessage = err ? err.message : "State error with peer"
    this.stateError(ctxMessage, msg)
  }
  
  dbError(msg, err) {
    let ctxMessage = err ? err.message : "State error with peer"
    this.stateError(ctxMessage, msg)
  }
  
  stateError(contextMessage, msg) {
    let last = Date(msg.last)
      , onTry = msg.try || 1
      , now = new Date()
    this.log.error(contextMessage, this.parms.minTime, onTry, last, JSON.stringify(msg))
    if (onTry > this.parms.maxTries) {
      this.log.error("Too many retries:", onTry)
//Fixme: how do we cancel the tally/chit now?
    }
    this.poll(onTry * this.parms.minTime * 1000)
  }

  dbProcess(msg, dbLogic, successCB, failureCB) {		//Call the database with state traffic
//this.log.trace("Database handler in peer2peer.js", msg, JSON.stringify(dbLogic))
    this.log.debug("Request DB process:", msg.target, 'action:', msg.action)
    if (!(['tally','chit','route','lift','chain'].includes(msg.target))) return
    this.db.query(`select mychips.${msg.target}_process($1,$2) as state;`, [msg, dbLogic], (err, res) => {
      if (err) {
        this.log.error('In query:', err.stack)
        if (failureCB) failureCB(err); else throw(err)
        if (this.closeDB) this.db.disconnect()
        return
      }
      let newState = res.rows[0]['state']
      this.log.debug("Result:", msg.action, '->', newState)
      if (newState) {
        if (successCB) successCB(newState, msg)
      } else {
        if (failureCB) failureCB({message: 'State processor failed'})
      }
    })
  }

  peerTransmit(msg, successCB, failureCB) {			//Transmit state traffic to the partner
    this.log.debug("P2P peerTransmit", msg.from.cid, '->', msg.to.cid, msg.to.agent)
    if (this.failSend) {				//Force transmission failure (for testing only)
      let c0 = this.failSend.charAt()
      if (c0 == 's') successCB()
      if (c0 == 'f') failureCB()
      this.log.debug("Generated error: suppressing send!", this.failSend)
    } else {
      this.peerNoise.send(msg, successCB, failureCB)
    }
  }
  
//  screen(obj, merge = {}, ...props) {		//Make a new object with only the required properties
//    let newObj = Object.assign({}, obj, merge)
//      , check = props.concat(Object.keys(merge)).concat(['target','action'])
//    Object.keys(newObj).forEach(k => {
//      if (!check.includes(k)) delete newObj[k]
//    })
//    return newObj
//  }

  query(req, data, cb) {				//Peer agents request data/actions here
this.log.debug("Noise peer query:", req, data)
    if (req == 'ticket') {
      this.db.query('select mychips.token_valid($1) as valid;', [data.token], (e, r)=>{
        if (e) {this.log.error('Error in token query:', e.message); return}
        if (r.rowCount == 1) {
          let row = r.rows[0]
//this.log.debug('Query res:', r, row)
          cb(row.valid)
        }
      })
    
//    } else if (req == 'x') {		//Do we need any other functions?
    } else {
      this.log.error('Unknown noise query:', req)
    }
  }

}		//class PeerCont

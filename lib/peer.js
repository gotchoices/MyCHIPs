//Peer to peer controller
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// Open a socket on a specified port to listen for connections from other peers.
// Also initiate various actions with other peers on appropriate asynchronous 
// triggers coming from the database.
// -----------------------------------------------------------------------------
// TODO:
//X- Spawn multiple instances of the server
//X- Initiate a dialog from the database on one instance
//X- Implement state processor for chits
//X- Can we ask the database for all pending notify events (in case server was not listening when the notify originally happened)
//- Fixme below: transition to failed state after too many retries, notify user
//- Could speed up whole retry cycle times to timeout in minutes instead of hours?
//- Leave connections open until they time out
//- Implement state processor for lifts
//- 
const { dbClient } = require('wyseman')
const { Log } = require('wyclif')
const Net = require('net')
const Tally = require('./tally')
const Chit = require('./chit')
const PeerComm = require('./peercomm.js')
const parmQuery = "select parm,value from base.parm_v where module = 'peers'"
const LongPoll = 3600000					//60 min
const ShortPoll = 60000						//60 sec

module.exports = class PeerCont {
  constructor(servConfig, dbConfig) {
    let hostID = servConfig.hostID
      , dbConf = {
      log: this.log,
      listen: ['parm_peers', 'mychips_peer' + (hostID ? '_' + hostID : '')],
    }
    Object.assign(dbConf, dbConfig)			//Merge in any user specified database arguments
    this.parms = {min_time: 5, max_tries: 4}		//In minutes
    this.pollTime = ShortPoll				//In msec
    
    this.log = Log('peer' + (this.hostID ? '-' + hostID : ''))
    this.log.info('Initializing peer server at port:', servConfig.port, 'Host ID:', hostID)

    this.peerComm = new PeerComm(servConfig.port, this.log, (serv, msg) => {
      this.log.debug('Incoming message from peer:', serv, 'Msg:', JSON.stringify(msg))
      if (msg.target in this.targets)				//If we have a handler for the specified target (tally, chit, etc.)
        if (msg.action in this.targets[msg.target])
          this.targets[msg.target][msg.action].call(this, msg)	//Call state handler
    })
    
    this.db = new dbClient(dbConf, (channel, payload) => {	//Initialize Database connection
      this.log.debug('Peer DB async on:', channel, payload)
      let msg
      if (payload) try {msg = JSON.parse(payload)} catch(e) {log.error("Parsing json payload: " + payload)}
      if (channel == 'parm_peers') {
        this.log.debug("Parameter", msg.target, "=", msg.value, msg)
        if (msg.target in this.parms && msg.value) {
          this.parms[msg.target] = msg.value
          this.poll()
        }

      } else if (msg && msg.target in this.targets) {		//If we have a handler for the specified target (tally, chit, etc.)
        if (msg.action in this.targets[msg.target])
          this.targets[msg.target][msg.action].call(this, msg)	//Call state handler
      }
      this.pollTime = ShortPoll					//Poll again quickly
    })

    this.closeDB=false
    this.targets = {}
    this.targets.tally = Tally
    this.targets.chit = Chit
//    this.targets.lift = Lift

    this.pollTimer = null
    this.db.query(parmQuery, (e,r)=>{
      if (e) {this.log.error('Getting peers parameters:', e.message); return}
this.log.debug('Peer got parms:', r.rows.length)
      r.rows.forEach(row => {
        let { parm, value } = row
        this.parms[parm] = value
      })
      if (servConfig.poll) this.poll()
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
    this.peerComm.close()
//this.log.trace("DB status:", this.db.client.activeQuery)
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
    this.log.error(contextMessage, this.parms.min_time, onTry, last, msg)
    if (onTry > this.parms.max_tries) {
      this.log.error("Too many retries:", onTry)
//Fixme: how do we cancel the tally/chit now?
    }
    this.poll(onTry * this.parms.min_time * 1000)
  }

  dbProcess(msg, dbLogic, successCB, failureCB) {		//Call the database with state traffic
//this.log.trace("Database handler in peer.js", msg, JSON.stringify(dbLogic))
    this.log.debug("Requested database action:", msg.action)
    if (!(['tally','chit','lift'].includes(msg.target))) return
    this.db.query(`select mychips.${msg.target}_process($1,$2) as state;`, [msg, JSON.stringify(dbLogic)], (err, res) => {
      if (err) {
        this.log.error('In query:', err.stack)
        if (failureCB) failureCB(err); else throw(err)
        if (this.closeDB) this.db.disconnect()
        return
      }
      let newState = res.rows[0]['state']
      this.log.debug("Result of", msg.action, ':', newState)
      if (newState) {
        if (successCB) successCB(newState, msg)
      } else {
        if (failureCB) failureCB({message: 'State processor failed'})
      }
    })
  }

  peerTransmit(msg, successCB, failureCB) {			//Transmit state traffic to the partner
    this.log.trace("In function peerTransmit in peer.js", msg)
    this.peerComm.send(msg.at, msg, successCB, failureCB)
  }
}		//class PeerCont

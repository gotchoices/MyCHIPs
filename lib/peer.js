//Peer to peer controller
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// Open a socket on a specified port to listen for connections from other peers.
// Also initiate various actions with other peers on appropriate asynchronous 
// triggers coming from the database.
// -----------------------------------------------------------------------------
// TODO:
//X- Spawn multiple instances of the server
//X- Initiate a dialog from the database on one instance
//- Leave connections open until they time out
//- Implement state processor for chits
//- Implement state processor for lifts
//- Can we ask the database for all pending notify events (in case server was not listening when the notify originally happened)
//- 
var log = require('./logger')('peer')
var { dbClient } = require('wyseman')
const Net = require('net')
const Tally = require('./tally')
const PeerComm = require('./peercomm.js')

module.exports = class PeerCont {
  constructor(port, hostID) {
    this.port = port
    this.hostID = hostID
    let dbConf = {
      logger: require('../lib/logger')('peer'),
      listen: 'mychips_peer' + (hostID ? '_' + hostID : ''),
      schema: __dirname + "/schema.sql"
    }

    this.peerComm = new PeerComm(port, (serv, msg) => {
      log.trace('Incoming message from peer:', serv, 'Msg:', msg)
      if (msg.target in this.targets)				//If we have a handler for the specified target (tally, chit, etc.)
        if (msg.action in this.targets[msg.target])
          this.targets[msg.target][msg.action].call(this, msg)	//Call state handler
    })
    
    this.db = new dbClient(dbConf, (channel, payload) => {	//Initialize Database connection
//log.debug('Async message from DB:', channel, payload)
      var msg = JSON.parse(payload)
      if (msg.target in this.targets)				//If we have a handler for the specified target (tally, chit, etc.)
        if (msg.action in this.targets[msg.target])
          this.targets[msg.target][msg.action].call(this, msg)	//Call state handler
    })

    this.targets = {}
    this.targets.tally = Tally
//    this.targets.chit = Chit
//    this.targets.lift = Lift
  }

  dbProcess(msg, dbLogic) {					//Call the database with state traffic
    log.trace("Database handler in peer.js", msg, dbLogic)
    if (!(['tally','chit','lift'].includes(msg.target))) return
    this.db.query(`select mychips.${msg.target}_state($1,$2,$3);`, [msg.user, msg.object, JSON.stringify(dbLogic)], (err, res) => {
      if (err) {log.debug(" Error:", err); return}
      let newState = res.rows[0][0]
      log.trace("newState:", newState)
    })
  }

  peerTransmit(msg) {						//Transmit state traffic to the partner
    log.trace("In function peerTransmit in peer.js", msg)
    this.peerComm.send(msg.at, msg)
  }

  userNotify(msg) {						//Notify our user of updates
    log.trace("Notify user of:", msg)
  }

}		//class PeerCont

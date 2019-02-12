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
//- Leave connections open until they time out
//- Implement state processor for lifts
//- Can we ask the database for all pending notify events (in case server was not listening when the notify originally happened)
//- 
const { dbClient } = require('wyseman')
const { Log } = require('wyclif')
const Net = require('net')
const Tally = require('./tally')
const Chit = require('./chit')
const PeerComm = require('./peercomm.js')

module.exports = class PeerCont {
  constructor(port, hostID, config) {
    this.port = port
    this.hostID = hostID
    this.log = Log('peer' + (hostID ? '-'+hostID : ''))
    this.log.info('Initializing peer server at port:', port, 'Host ID:', hostID)
    let dbConf = {
      log: this.log,
      listen: 'mychips_peer' + (hostID ? '_' + hostID : ''),
      schema: __dirname + "/schema.sql"
    }
    Object.assign(dbConf, config)				//Merge in any user specified database arguments
    this.peerComm = new PeerComm(port, this.log, (serv, msg) => {
      this.log.debug('Incoming message from peer:', serv, 'Msg:', JSON.stringify(msg))
      if (msg.target in this.targets)				//If we have a handler for the specified target (tally, chit, etc.)
        if (msg.action in this.targets[msg.target])
          this.targets[msg.target][msg.action].call(this, msg)	//Call state handler
    })
    
    this.db = new dbClient(dbConf, (channel, payload) => {	//Initialize Database connection
    this.log.debug('Async message from DB:', channel, payload)
      var msg = JSON.parse(payload)
      if (msg.target in this.targets)				//If we have a handler for the specified target (tally, chit, etc.)
        if (msg.action in this.targets[msg.target])
          this.targets[msg.target][msg.action].call(this, msg)	//Call state handler
    })
    this.closeDB=false
    this.targets = {}
    this.targets.tally = Tally
    this.targets.chit = Chit
//    this.targets.lift = Lift
  }	//Constructor
  
  close() {							//Shut down this controller
    this.peerComm.close()
//this.log.trace("DB status:", this.db.client.activeQuery)
    if (this.db.client.activeQuery) {				//Is there a query in process?
      this.closeDB = true
    } else {
      this.db.disconnect()
    }
  }

  dbProcess(msg, dbLogic, successCB, failureCB) {		//Call the database with state traffic
//this.log.trace("Database handler in peer.js", msg, dbLogic)
    this.log.debug("Requested database action:", msg.action)
    if (!(['tally','chit','lift'].includes(msg.target))) return
    this.db.query(`select mychips.${msg.target}_process($1,$2) as state;`, [msg, JSON.stringify(dbLogic)], (err, res) => {
      if (err) {
        this.log.error('In query:', err.stack)
        if (failureCB) {failureCB(err)} else {throw(err)}
        if (this.closeDB) this.db.disconnect()
        return
      }
      let newState = res.rows[0]['state']
      this.log.trace("newState:", newState)
      if (successCB) successCB()
    })
  }

  peerTransmit(msg, successCB, failureCB) {			//Transmit state traffic to the partner
    this.log.trace("In function peerTransmit in peer.js", msg)
    this.peerComm.send(msg.at, msg, successCB, failureCB)
  }
}		//class PeerCont

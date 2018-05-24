//Peer to peer controller
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// Open a socket on a specified port.  Listen for connections from other peers.
// Also initiate various actions with other peers on appropriate asynchronous 
// triggers coming from the database.
// -----------------------------------------------------------------------------
// TODO:
//X- Open listening socket
//X- Design a few simple state transition dialogs
//X- Allow to set database host and port from the daemon command line (fix admin.js too)
//X- More sustainable way to specify schema name (schema1.sql)
//X- Create configurable state handler for each dialog
//X- Open connection object to individual peers on demand
//- Leave connections open until they time out
//X- Spawn 2 instances of the server
//X- Initiate a dialog from the database on one instance
//- Parse incoming packets (dialog, request, data)
//- 
var log = require('./logger')('peer')
var { dbClient } = require('wyseman')
const Net = require('net')
const States = require('./states')
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
    })
    
    this.db = new dbClient(dbConf, (channel, payload) => {	//Initialize Database connection
log.debug('Async from DB:', channel, payload)
      var msg = JSON.parse(payload)
      if (msg.target in this.targets)
        this.targets[msg.target].handle(msg.action, msg)
    })

    this.targets = {}
    this.targets.tally = new States(this, Tally, this.database)
//    this.targets.chit = new States(this, Chit, this.database)
//    this.targets.lift = new States(this, Lift, this.database)

//Debugging:
//    this.db.query("select ent_name from mychips.users_v", (err,res) => {
//      if (err) log.debug(" Error:", err); else log.debug(" Result:", res.rows)
//    })
  }
  
  database(msg, dbLogic) {
    log.trace("Database handler in peer.js", msg, dbLogic)
    if (!(['tally','chit'].includes(msg.target))) return
//log.trace("json:", JSON.stringify(dbLogic))
    this.db.query(`select mychips.${msg.target}_state($1,$2,$3);`, [msg.user, msg.guid, JSON.stringify(dbLogic)], (err, res) => {
      if (err) {log.debug(" Error:", err); return}
      let newState = res.rows[0][0]
      log.trace("newState:", newState)
    })
  }

  peerTransmit(msg) {
    log.trace("In function peerTransmit in peer.js", msg)
    this.db.query("select json,peer_sock from mychips.tallies_v where tally_ent = $1 and tally_guid = $2", [msg.user, msg.guid], (err, res) => {
      if (err) {log.debug(" Error:", err); return}
      let tally = res.rows[0].json
      log.trace("Tally:", tally)
      this.peerComm.send(res.rows[0].peer_sock, tally)
    })
  }

}		//class PeerCont

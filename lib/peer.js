//Peer to peer controller
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// Open a socket on a specified port.  Listen for connections from other peers.
// Also initiate various actions with other peers on appropriate asynchronous 
// triggers coming from the database.
// -----------------------------------------------------------------------------
// TODO:
//X- Open listening socket
//- Design a few simple state transition dialogs
//- Spawn 2 instances of the server
//- Initiate a dialog from the database on one instance
//- 
//- Parse incoming packets (dialog, request, data)
//- Create configurable state handler for each dialog
//- Allow to set database host and port from the daemon command line (fix admin.js too)
//- 
var log = require('./logger')('peer')
var { dbClient } = require('wyseman')
const Net = require('net')

module.exports = class PeerCont {
  constructor(port) {
    this.port = port
    let dbConf = {
      logger: require('../lib/logger')('peer'),
      listen: 'foo',
      schema: __dirname + "/schema-1.sql"
    }

    this.server = Net.createServer(sock => {
      log.trace('Peer connected:', port)

      sock.on('data', function(data) {
log.debug('Data:', data.toString())
      })

      sock.on('end', () => {log.trace('Disconnected:', port)})
      sock.on('error', err => {log.error('Socket error:', err.message)})
    }).listen(port)
    
    this.db = new dbClient(dbConf, (channel, payload) => {
log.debug('Async from DB:', channel, payload)
    })

//Debugging:
    this.db.query("select ent_name from mychips.users_v", (err,res) => {
      if (err) log.debug(" Error:", err); else log.debug(" Result:", res.rows)
    })
  }

}

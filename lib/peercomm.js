//Auto-managed bi-directional connection to multiple peers
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// Prepare to communicate on demand with a remote host at a specified IP number
// and socket number.  If we get a connection from the specified host, that
// open channel will serve the same purpose as a channel initiated from this end.
// -----------------------------------------------------------------------------
// TODO:
//X- Open initial server
//X- If we get a connection, record it as a tentative, unchecked channel
//X- First message should be an ID record from the remote end
//X- If the IP number is the same as our peer, accept it and mark channel as open
//X- Otherwise, report it, and close the channel
//X- If we get a call to send, check for already open channel
//X- If none, initialize one, record it as the current channel
//X- Send an opening message with our ID
//- Any time a channel is opened, set a timer to automatically close it
//- Any time we have valid send/receive, prolong the timeout timer
//- 
var log = require('./logger')('socket')
var peers = {}						//Keep track of which peers we are connected to
const Net = require('net')

module.exports = class PeerSocket {
  constructor(port, messageCB) {
    this.port = port
//log.debug('Initializing peer pool:', port)

    this.server = Net.createServer(sock => {		//Initialize server to receive peer connections
      log.trace('Peer initiated connection at:', port, ' from:', sock.remoteAddress)
      let remoteAddress = sock.remoteAddress
        , remoteServer = null				//Not verified yet

      sock.on('data', function(data) {
        let msg = data.toString().trim()
          , ip = sock.remoteAddress
        if (!remoteServer) {				//First line should tell us who is connecting (@server_port)
log.trace("First line:", msg)
          let port = msg.slice(1)			//Skip over first character
          if (msg.slice(0,1) != '@' || !(/^\d+$/.test(port))) {
            log.error("Invalid port handshake:", msg)
            sock.end(); return				//We didn't get a valid looking socket address from the peer
          }
          if (Net.isIPv4(ip)) {
              remoteServer = sock.remoteAddress + ':' + port
          } else if (Net.isIPv6(ip)) {
              remoteServer = '[' + sock.remoteAddress + ']:' + port
          } else {
            log.error("Unrecognized IP format:", ip)
            sock.end(); return				//We didn't get required socket address format on first line
          }
          peers[remoteServer] = sock			//Note socket address so we can write to it asynchronously
        } else {					//For all other lines other than the first one
//          log.debug(' Remote data from ', remoteServer, '=>' , JSON.parse(msg))
          messageCB(remoteServer, JSON.parse(msg))
        }
      })

      sock.on('end', () => {
        log.trace('Server disconnect:', port, remoteServer)
        peers[remoteServer] = null
      })
      sock.on('error', err => {log.error('Socket error:', err.message)})
    }).listen(port)
  }		//constructor()
  
  send(peer, msg) {			//Try to send to a peer, who may or may not be connected
    if (peers[peer]) {
      log.trace('Will send to:', peer, 'Message:', msg)
      peers[peer].write(msg)
      return
    }
    log.trace('Attempting to open connection to:', peer)
    let [ ip, port ] = peer.split(':')
    let client = Net.createConnection(port, ip, () => {
      client.write('@' + this.port)
      peers[peer] = client
//log.trace('Sending:', JSON.stringify(msg))
      client.write(JSON.stringify(msg))
    })
    client.on('error', data => {
      log.trace('Failed to open connection to:', peer)
//Fixme: should initiate some kind of retry schedule
    })
    client.on('data', data => {
      messageCB(remoteServer, JSON.parse(msg))
    })
    client.on('end', () => {
      log.trace('Client disconnect:', port, peer)
      peers[peer] = null
    })
  }		//send()

}		//class PeerSocket

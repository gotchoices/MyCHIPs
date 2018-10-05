//Auto-managed bi-directional connection to multiple peers
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// Prepare to communicate on demand with a remote host at a specified IP number
// and port number.  If we already have an open connection with the specified 
// host, that channel can serve the purpose so no new connection is needed.
// If a peer connects to us, we will disconect that session after a timeout.
// -----------------------------------------------------------------------------
// TODO:
//X- Send an opening message with our ID
//X- What if multiple packets come in a single message?
//- Any time a channel is opened, set a timer to automatically close it
//- Any time we have valid send/receive, prolong the timeout timer
//- 
var log = require('./logger')('peercomm')
const Net = require('net')
const Timeout = 60000					//Keep connections open for 1 minute

module.exports = class PeerSocket {
  constructor(port, messageCB, timeout = Timeout) {
    this.port = port
    this.messageCB = messageCB
    this.timeout = timeout
    this.peers = {}					//Keep track of which peers we are connected to
    this.timers = {}
//log.debug('Initializing peer server at port:', port)

    this.server = Net.createServer(sock => {		//Initialize server to receive peer connections
      log.trace('Peer initiated connection at:', port, ' from:', sock.remoteAddress)
      let remoteAddress = sock.remoteAddress
        , remoteServer = null				//Not verified yet

      sock.on('data', (data) => {
        let msg		= data.toString().trim()
          , ip		= sock.remoteAddress
          , msgs	= msg.split(/\r?\n/)		//Split in case we have multiple messages

        if (!remoteServer) {				//First line should tell us who is connecting (@server_port)
          let msg = msgs[0]				//Grab first packet
            , port = msg.slice(1)			//Skip over first character
log.trace("First line:", msg)
          msgs = msgs.slice(1)				//Remember all but first message
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
          this.peers[remoteServer] = sock		//Note socket address so we can write to it asynchronously
        }

        msgs.forEach((msg) => {				//Process any additional messages
//          log.debug(' Remote data from ', remoteServer, '=>' , JSON.parse(msg))
          this.messageCB(remoteServer, JSON.parse(msg))
        })

        if (!(remoteServer in this.timers)) this.timers[remoteServer] = null
        if (this.timers[remoteServer]) clearTimeout(this.timers[remoteServer])	//Clear any timeout timer
        this.timers[remoteServer] = setTimeout(() => {				//And set a new one
          sock.end();
          delete this.peers[remoteServer]
          this.timers[remoteServer] = null
        }, this.timeout)
      })

      sock.on('end', () => {
        log.trace('Server disconnect:', port, remoteServer)
        delete peers[remoteServer]
      })

      sock.on('error', err => {log.error('Socket error:', err.message)})

    }).listen(port)
  }		//constructor()

  close(peer) {
    if (this.peers[peer]) {
      this.peers[peer].end()
    }
  }

  send(peer, msg, successCB, failureCB) {		//Try to send to a peer, who may or may not be connected
    if (this.peers[peer]) {
      log.trace('Will send to already connected peer:', peer, 'Message:', msg)
      this.peers[peer].write(JSON.stringify(msg), 'utf8', successCB)
      return
    }

    log.trace('Attempting to open new connection to peer:', peer)
    let [ ip, port ] = peer.split(':')

    let client = Net.createConnection(port, ip, () => {
      client.write('@' + this.port + "\n")
      this.peers[peer] = client
//log.trace('Sending:', JSON.stringify(msg))
      client.write(JSON.stringify(msg), 'utf8', successCB)
    })

    client.on('error', data => {
      log.trace('Failed to open connection to:', peer)
      if (failureCB) failureCB()
    })
    client.on('data', msg => {
      this.messageCB(peer, JSON.parse(msg))
    })
    client.on('end', () => {
      log.trace('Client disconnect:', port)
      this.peers[peer] = null
    })
  }		//send()

}		//class PeerSocket

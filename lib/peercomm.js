//Auto-managed bi-directional connection to multiple peers
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// Prepare to communicate on demand with a remote host at a specified IP number
// and port.  If we already have an open connection with the specified address, 
// just use that channel--no new connection is needed.  If the connection was
// initiated by another peer, we will disconect after specified a timeout.
// -----------------------------------------------------------------------------
// TODO:
//X- Send an opening message with our ID
//X- What if multiple packets come in a single message?
//- Implement noise protocol over the connection
//- Make timeouts adaptive.  The more we connect to a certain address, the longer the timeouts
//- socket.remoteAddress does not always reflect where an outbound connection would reach the peer
//  (like if the server is on a VM).  Can we get a more reliable idea of where an incoming connection is coming from?
//- Any time a channel is opened, set a timer to automatically close it
//- Any time we have valid send/receive, prolong the timeout timer
//- 
const { Log } = require('wyclif')
const Net = require('net')
const Frame = require('frame-stream')		//Delimit packets over TCP
const DefaultTimeout = 60000				//Keep connections open for 1 minute
const DefaultPort = 65430

module.exports = class PeerSocket {
  constructor(config, messageCB) {
    this.port = config.port || DefaultPort		//Port we listen to
    this.messageCB = messageCB				//Call this when we receive data
    this.timeout = config.timeout || DefaultTimeout
    this.encrypt = (config.encrypt === undefined) ? true : config.encrypt
    this.peers = {}					//Keep track of which peers we are connected to
    this.timers = {}
    this.log = config.log || Log('peercomm')
    this.log.debug('Initializing peer communications at port:', this.port)

    this.server = Net.createServer(sock => {		//Initialize server to receive peer connections
this.log.debug('Peer initiated connection at:', this.port, ' from:', sock.remoteAddress)
      let remoteServer = null				//Not verified yet
        , fsock = this.initFraming(sock)

      fsock.on('data', (data) => {			//When data comes in
        let msg		= data.toString().trim()
          , ipAddr	= sock.remoteAddress
          , msgs	= msg.split(/\r?\n/)		//Split in case we have multiple messages

this.log.trace("Data:", remoteServer)
        if (!remoteServer) {				//First line should tell us who is connecting (@server_port)
          let msg = msgs[0]				//Grab first packet
            , port = msg.slice(1)			//Skip over first character
this.log.trace("First line:", msg)
          msgs = msgs.slice(1)				//Remember all but first message
          if (msg.slice(0,1) != '@' || !(/^\d+$/.test(port))) {
            this.log.error("Invalid port handshake:", msg)
            sock.end(); return				//We didn't get a valid looking socket address from the peer
          }
//this.log.debug("Remote:", ipAddr, port)
          if (Net.isIPv4(ipAddr)) {
            remoteServer = ipAddr + ':' + port
          } else if (Net.isIPv6(ipAddr)) {
            remoteServer = '[' + ipAddr + ']:' + port
          } else {
            this.log.error("Unrecognized IP format:", ipAddr)
            sock.end(); return				//We didn't get required socket address format on first line
          }
          this.peers[remoteServer] = sock		//Note socket address so we can write to it asynchronously
        }

        msgs.forEach((m) => {				//Process any additional messages
          let msg
          if (m) try {msg = JSON.parse(m)} catch(e) {log.error("Parsing json message: " + m)}
this.log.trace(' Remote data from ', remoteServer, '=>' , m)
          if (msg) this.messageCB(remoteServer, msg)
        })

        if (!(remoteServer in this.timers)) this.timers[remoteServer] = null
        if (this.timers[remoteServer]) clearTimeout(this.timers[remoteServer])	//Clear any timeout timer
        this.timers[remoteServer] = setTimeout(() => {				//And set a new one
          sock.end();
          delete this.peers[remoteServer]
          this.timers[remoteServer] = null
        }, this.timeout)
      })

      fsock.on('end', () => {
        this.log.warn('Server disconnect:', this.port, remoteServer)
        delete this.peers[remoteServer]
      })

      fsock.on('error', err => {this.log.error('Socket error:', err.message)})

    }).listen(this.port)
  }		//constructor()

  close() {
    this.log.debug('Closing server on port:', this.port)
    this.server.close()				//Quit listening for incoming connections
    Object.keys(this.peers).forEach((key) => {	//And close any open connections we may have
      if (this.timers[key]) clearTimeout(this.timers[key])
      this.peers[key].end()
    })
  }
  
  end(peer) {					//Close any incoming socket with the specified peer
    if (this.peers[peer]) {this.peers[peer].end()}
  }

  initFraming(socket) {			// Configure socket to handle complete, delimited messages
    let s = socket.pipe(Frame.decode())		//Process stream as complete messages
      , encode = Frame.encode()
    encode.pipe(socket)
    socket.encode = encode			//Write to fwrite method to frame our messages
    return s
  }

  send(peer, msg, successCB, failureCB) {	//Try to send to a peer, who may or may not be connected
    if (!peer) return failureCB()
this.log.trace('Send:', peer, msg)
    if (this.peers[peer]) {
      this.log.trace('Will send to already connected peer:', peer, 'Message:', msg)
      this.peers[peer].encode.write(JSON.stringify(msg), 'utf8', successCB)
      return
    }

    this.log.debug('Attempting to open new connection to peer:', peer)
    let [ ip, port ] = peer.split(':')

    let client = Net.connect(port, ip, () => {		//Connect to peer as client
      let fclient = this.initFraming(client)
this.log.trace('Sending:', '@' + this.port)
      client.encode.write('@' + this.port)
      this.peers[peer] = client
this.log.trace('Sending:', JSON.stringify(msg))
      client.encode.write(JSON.stringify(msg), 'utf8', successCB)

      fclient.on('data', m => {					//When a message comes in
        let msg
        if (m) try {msg = JSON.parse(m)} catch(e) {
          log.error("Parsing json message: " + m)
          if (failureCB) failureCB()
        }
        if (msg) this.messageCB(peer, msg)
      })
      fclient.on('error', data => {
        this.log.error('Failed to open connection to:', peer)
        if (failureCB) failureCB()
      })
      fclient.on('end', () => {					//When connection terminated
        this.log.warn('Client disconnect:', port)
        this.peers[peer] = null
      })
    })
  }		//send()

}		//class PeerSocket

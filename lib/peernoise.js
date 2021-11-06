//Bidirectional encrypted connection to multiple peers
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// Manages communication on demand with a remote host at a specified address
// and port.  If there is already an open connection with the specified address, 
// just use that channel--no new connection is needed.  If the connection was
// initiated by another peer, we will disconnect after specified a timeout.
// TRIP HAZARD: In this context, "peer" refers to peer sites--not peer users!
// -----------------------------------------------------------------------------
// TODO:
//X- But do save/cache peer keys
//X- Clean up the way we call query(key)
//X- Test fresh non-I connection to an uncached peer (but with key available through query)
//X- Are encrypt and siteKey switches redundant?	Yes, get rid of encrypt switch
//- Need to delete manager peer key cache entry if the key ever fails
//- Implement (or remove) queue functionality
//- When might messages need to be queued?
//- Implement non-encrypted mode (separate class for encrypted/non-encrypted)
//- Make timeouts adaptive?  The more we connect to a certain address, the longer the timeouts
//- Other Fixme's below
//- 
const Os = require('os')
const Net = require('net')
const Url = require('url')
const { Log } = require('wyclif')		//Default logging
const ObjectSet = require('./objectset')
const NoiseWrap = require('./noisewrap.js')		//Wrapper over Noise routines
const { Address6 } = require('ip-address')
const Frame = require('frame-stream')		//Delimit packets over TCP
const DefaultTimeout = 60000			//Keep connections open for 1 minute
const TimeoutIncrement = 30000
const DefaultPort = 65430
const Encoding = 'utf8'

class PeerConnection {		//One of these for each new connection with a peer
  constructor(peer, socket, manager) {
    this.manager = manager			//parent object
    this.log = manager.log || (()=>null)
//    this.queue = []				//pending messages; Fixme: do we need this?
    this.state = 'none'				//No validated connecton yet
    this.n = new NoiseWrap({log: this.log})
    
    if (peer && !socket) {			//The manager must initiate the connection by calling this.send()
      this.setPeer(peer)
this.log.debug('New PC; peer:', this.peerAddr, this.peerPort, this.state)
      this.initiator = true			//We can send:I,N,K,T; receive:A,T
      this.peerKey = manager.peerKey(peer)	//Do we already know the other guy's key?

    } else if (!peer && socket) {		//Unidentified peer connected to us as a client
this.log.debug('New PC; addr:', socket.remoteAddress)
      let s = this.initFraming(socket)		//Process stream as complete messages
      this.resetTimeout(manager.timeout)	//We are responsible for disconnect timeouts
      this.initiator = false			//We can send:A,T; receive:I,N,K,T
      this.peerKey = null

      s.on('data', d=>this.fromInitiator(d))	//When data comes in
      s.on('error', e => {this.log.error('Socket error:', this.peer, e.message)})
      s.on('end', () => this.socketEnd())
    }		//if
  }		//constructor

  setPeer(peer) {	//---- Set remote peer data
    let url = Url.parse("x://" + peer)		//Separate port and hostname (IP)
    this.peer = peer
    this.peerPort = url.port
    this.peerAddr = url.hostname
  }

  packetParse(message) {	//---- Interpret an incoming message as JSON content
    let messageObj, messageText = message
    if (Buffer.isBuffer(message)) {		//Convert buffer to text
        if (message.length <= 0) return null
        messageText = Buffer.from(message)
    }
    if (!messageText || messageText == '') return null
    try {messageObj = JSON.parse(messageText)} catch(e) {
      this.log.error("Parsing json message:", messageText, e.message)
    }
    return messageObj
  }

  eatNoise(packet, initiator, validHeaders, cb) {	//---- Parse NPF packet if it matches a specified header
    let header = packet.slice(0,1).toString()		//Point to the header character
      , data = packet.slice(1)				//Data in the rest of the packet
      , receiveBuf = Buffer.alloc(packet.byteLength)	//Plaintext should be shorter than encrypted
        
    if (!validHeaders.includes(header)) return false	//Ignore unexpected packet types
this.log.debug('eatNoise:', header, validHeaders)
    if (initiator !== null) {				//Initiator true or false: initiate noise state
      let hs1 = "IKN".includes(header) ? header : 'K'	//Expecting only I,K,N packets
        , handshake = hs1 + (hs1 == 'N' ? '' : 'K')	//Build handshake IK, KK, N
        , peerKey = hs1 == 'K' ? this.peerKey : null
this.log.debug('preNoise:', hs1, handshake, this.peerKey, peerKey)
      this.noiseState = this.n.initialize(handshake, initiator, this.manager.siteKey, peerKey)
    }
    this.split = this.n.readMessage(this.noiseState, data, receiveBuf)
this.log.debug('postNoise:', this.noiseState, this.n.readMessage.bytes, receiveBuf.slice(0,this.n.readBytes).toString(), 'split:', this.split)
    if (cb) cb(header, this.packetParse(receiveBuf.slice(0, this.n.readBytes)))
    return true
  }

  spewNoise(header = 'A', message = '', state = this.noiseState) {  	//---- Create and send NPF acknowledge packet
    let messageBuf = Buffer.from(message)
      , packetBuf = Buffer.alloc(messageBuf.byteLength + this.n.BufferAdd)
      , noiseBuf = packetBuf.slice(1)		//Write noise data after header
    packetBuf.write(header)
    this.split = this.n.writeMessage(state, messageBuf, noiseBuf)
    this.encode.write(packetBuf.slice(0,this.n.writeBytes + 1))
this.log.debug('Spew:', header, packetBuf.slice(0,this.n.writeBytes).toString('hex'), 'split:', !!this.split)
  }

  resetTimeout(defaultTimeout) {	//---- Set alarm to close channel if not used within time
    let time = this.manager.peerTimeout(this.peer, defaultTimeout) || DefaultTimeout
    if (this.timer) clearTimeout(this.timer)		//Clear any timeout timer
    this.timer = setTimeout(() => {			//And set a new one
      this.end()
    }, time)
  }

  fromInitiator(packet) {	//---- Handle incoming data (I,N,K,T) from a client
    this.resetTimeout()
  
    if (this.state == 'open') {			//T only
this.log.debug('Got packet on open channel:', packet)
      this.decrypt(packet)

    } else if (this.state == 'none') {		//First packet, should be I or N
      this.eatNoise(packet, false, ['I','N'], (header, data) => {
this.log.debug('Got first packet:', header, data)
        if (header == 'N') {
          this.state = 'id'
          this.peer = data			//Record the peer address:port
          this.peerKey = this.manager.peerKey(this.peer)	//See if peer's key in the cache
this.log.debug('Got N packet:', data, 'peerKey:', this.peerKey)
          
        } else if (header == 'I') {
this.log.debug('Got I packet:', data)
          let ticket = data.ticket		//Grab any ticket out of message
          delete data.ticket
          this.state = ticket
          this.manager.query('ticket', ticket, () => {	//Have app validate ticket
            this.setPeer(data.peer)		//Record the peer address:port
            this.spewNoise()			//Acknowledge completes noise connection
            this.state = 'open'
            this.peerKey = Buffer.from(this.noiseState.rs)	//Make copy of peer's public key
            this.manager.peerKey(this.peer, this.peerKey)	//Cache key with our manager
this.log.debug('Noting peer:', data.peer, this.peerKey.toString('hex'))
            this.manager.query('store', {peer: this.peer, key: this.peerKey})	//Store with the app
            this.n.destroy(this.noiseState)
            if (data && Object.keys(data).length >= 1)	//Process message if any
              this.manager.messageCB(this,data)
          })	//query
        }	//if header
      })	//eatNoise()

    } else if (this.state == 'id') {		//expecting a K packet
this.log.debug('Packet on pending channel:', packet, 'peerKey:', this.peerKey)

      let kOnly = ['K']
        , callBack = (header, data) => {		//Call on eatNoise success
this.log.debug('Packet:', header, data, 'peerKey:', this.peerKey)
        this.state = 'open'
        this.spewNoise()			//Acknowledge completes noise connection
        if (data && Object.keys(data).length >= 1)	//Process message if any
          this.manager.messageCB(this,data)
      }
      if (this.peerKey) {				//We have a key for this peer
        this.eatNoise(packet, false, kOnly, callBack)
      } else if (!this.manager.query('key', this.peer, key => {	//Else query app for it
        if (this.peerKey = key) {
          this.manager.peerKey(this.peer, this.peerKey)		//Cache peer key
          this.eatNoise(packet, false, kOnly, callBack)
        } else {
          this.log.error('Peer validation failed for:', this.peer)
        }
      })) {
        this.log.error('No peer validation function')
      }

    } else {		//state = request or ticket
this.log.error('Unexpected packet:', header, data)
    }
  }		//fromInitiator

  fromResponder(packet) {	//---- Handle incoming data (A,T) from a server
this.log.debug('Server message:', this.state, packet.slice(0,1).toString(), packet.toString('hex'))

    if (this.state == 'open') {			//Should get T only
      this.decrypt(packet)

    } else if (this.state == 'pending') {	//Should get A only
      this.eatNoise(packet, null, ['A'], (header, data) => {
this.log.debug('Ate packet:', header, data)
        if (header == 'A') {			//Got acknowledge
          this.state = 'open'			//Channel now open
          this.n.destroy(this.noiseState)
          if (data && Object.keys(data).length <= 1)	//If any data came along, process it
            this.manager.messageCB(this, data)
        }
      })
    }

  }	//fromResponder

  peerAddress() {		//---- Get remote IP address socket is connected to
this.log.debug("Peer address:", this.peer)
    if (!this.fromAddress) {
      if (this.socket.remoteFamily == 'IPv6') {
        this.fromAddr = new Address6(this.socket.remoteAddress).correctForm()
      } else {
        this.fromAddr = Address6.fromAddress4(this.socket.remoteAddress).correctForm()
      }
    }
    return this.fromAddr
  }	//fromAddress
  
  end() {			//---- Close this connection
    if (this.timer) clearTimeout(this.timer)
    if (this.socket) this.socket.end()
this.log.debug("Ending peer connection:", this.peer)
    this.manager.forget(this)
  }
  
  socketEnd() {			//---- Handle unexpected end event
    this.log.warn('Socket disconnected:', this.peer)
    this.socket = null
    this.end()
  }

  initiate(messageObj, successCB, failureCB) {	//---- Begin a noise connection
    let ticket = messageObj.ticket
this.log.debug('Initiate:')
    if (ticket) {				//If connecting by ticket
this.log.debug('Ticket initiate:', ticket.key)
      this.peerKey = ticket.key			//the ticket must contain a key
    } else if (!this.peerKey) {		//If we don't have a key, get one from the calling application
this.log.debug('No peer key, try to query app')
      if (!this.manager.query('key', this.peer, key => {
        if (this.peerKey = key) {		//Note the key and retry
this.log.trace('Retrying:', key)
          this.initiate(messageObj, successCB, failureCB)	//Call ourselves recursively
        } else {			//If no key found, give up
          this.log.error('Failure to locate ticket credentials:', key)
          if (failureCB) failureCB()
        }
      })) {
        this.log.error('No peer validation function found')
      }
      return
    }		//if ticket
   if (this.peerKey) {			//Cache peer's key
     this.manager.peerKey(this.peer, this.peerKey)
   } else {
      this.log.error("idNoise: Tried to initiate noise without peer Key")
      return
   }

this.log.debug('Initializing noise:', this.manager.siteKey, this.peerKey, messageObj)
    let hs1 = ('ticket' in messageObj) ? 'I' : 'K'	//Handshake first character
      , messageBuf = Buffer.from(JSON.stringify(messageObj))
      , packetBuf = Buffer.alloc(messageBuf.byteLength + this.n.BufferAdd)
      , noiseBuf = packetBuf.slice(1)		//Noise starts after header character

this.log.debug('Try Noise:', hs1, packetBuf.length, this.peerKey)
    if (hs1 == 'K') {		//First send an N record with node ID
      let header = 'N'
        , ns = this.n.initialize(header, true, this.manager.siteKey, this.peerKey)
      this.spewNoise(header, '"'+this.manager.peer+'"', ns)
      this.n.destroy(ns)
    }
    this.noiseState = this.n.initialize(hs1 + 'K', this.initiator = true, this.manager.siteKey, this.peerKey)
    this.split = this.n.writeMessage(this.noiseState, messageBuf, noiseBuf)
this.log.debug('Noise generates split:', typeof this.split)

    packetBuf.write(hs1)				//Packet header
this.log.debug('Writing bytes:', this.n.writeBytes)
    this.encode.write(packetBuf.slice(0, this.n.writeBytes + 1), null, successCB)
    this.state = 'pending'
  }
  
  decrypt(packet) {		//---- Decrypt, parse and process a T message
    let header = packet.slice(0,1).toString()
      , messageBuf = packet.slice(1)
      , decryptBuf = Buffer.alloc(packet.byteLength)	//Plaintext should be shorter than this

    if (header != 'T') return			//Ignore invalid packets
this.log.debug('Got packet:', header, messageBuf.toString('hex'), messageBuf.byteLength)
//this.log.debug("RX:", this.split.rx.toString('hex'))
    if (!this.split || !this.split.rx) {
      this.log.error('No decryption key found')
    } else {
      this.n.decrypt(this.split.rx, decryptBuf, messageBuf)
this.log.debug('Decrypted:', header, decryptBuf.toString())
      let messageObj = this.packetParse(decryptBuf.slice(0, this.n.decryptBytes))
      this.manager.messageCB(this, messageObj)
    }
  }

  encrypt(messageObj, successCB, failureCB) {	//---- Encrypt and send a message
    let message = Buffer.from(JSON.stringify(messageObj))
      , packetBuf = Buffer.alloc(message.byteLength + this.n.BufferAdd)
      , encryptBuf = packetBuf.slice(1)
    if (!this.split || !this.split.tx) {
      this.log.error('No encryption key found')
    } else {
      this.n.encrypt(this.split.tx, encryptBuf, message)
      let sendBuf = packetBuf.slice(0, this.n.encryptBytes + 1)
      sendBuf.write('T')
this.log.debug('Write:', sendBuf.toString('hex'))
      this.encode.write(sendBuf, Encoding, successCB)
    }
  }
  
  send(messageObj, successCB, failureCB) {	//---- Send a message, opening the connection first if necessary
this.log.debug('In PC send; state:', this.state)
    if (this.state == 'open') {			//Channel is already open, can just write message
      this.encrypt(messageObj, Encoding, successCB)
      return true
    }
//Fixme: need this?
//    this.queue.push({messageObj, successCB, failureCB})	//Save message until channel opens

    if (this.state != 'none') {
//Fixme: should I set a timer in case opening doesn't resolve?
this.log.debug('Found pending state:', this.state)

    } else {				//state == none; Need to initiate a noise connection
      if (!this.peerAddr || !this.peerPort) {
        if (failureCB) failureCB()
        return false
      }
      let client = Net.connect(this.peerPort, this.peerAddr, () => {	//Connect to peer as client
        let s = this.initFraming(client)	//Process stream as complete messages

this.log.debug('Connected as client to:', this.peer)
        s.on('data', d=>this.fromResponder(d))	//When data comes in
        s.on('error', e => {this.log.error('Socket error:', this.peer, e.message)})
        s.on('end', () => this.socketEnd())

        if (!('peer' in messageObj)) messageObj.peer = this.manager.peer	//Provide our ID to the other peer
        this.initiate(messageObj, successCB, failureCB)
      })	//connect
    }		//if
    return true
  }		//send

  initFraming(socket) {	//---- Configure socket to handle complete, delimited messages
    let s = socket.pipe(Frame.decode())	//Process stream as complete messages
    this.encode = Frame.encode()		//Write to encode method to frame our messages
    this.encode.pipe(socket)
    this.socket = socket
    return s
  }

}		//peerConnection


module.exports = class PeerServer {		//Connection server side, listener/responder
  constructor(config, messageCB) {
    this.address = config.address || Os.hostname()	//Our address for other peers
    this.port = config.port || DefaultPort		//Port we listen to
    this.peer = this.address + ':' + this.port
    this.messageCB = messageCB				//Call this when we receive data
    this.timeout = config.timeout || DefaultTimeout
    this.siteKey = config.siteKey
    this.queryCB = config.queryCB || (()=>null)	//Call to query for keys, tokens, tallies
    this.connections = new ObjectSet()			//Keep list of current peer sockets
    this.log = config.log || Log('peercomm')
    this.log.debug('Peercomm server listening on port:', this.port)
    this.peerData = {}					//Cache info about peers
    this.peerDataDefault = () => ({timeout: this.timeout})

    this.server = Net.createServer(sock => {		//Initialize server to receive connections from peer clients
this.log.debug('Peer initiated connection on:', this.port, ' from:', sock.remoteAddress)
      let pc = new PeerConnection(null, sock, this)
      this.connections.add(pc)				//Register in our collection
    }).listen(this.port)
  }	//constructor()

  peerKey(peer, value) {	//---- Get/set cached value for peer public key
    let pd = this.peerData[peer]
    if (!pd) pd = this.peerData[peer] = this.peerDataDefault()
    if (value) pd.peerKey = value
    return pd.peerKey
  }
  
  peerTimeout(peer, value) {	//---- Get/set cached value for peer adaptive timeout value
    let pd = this.peerData[peer]
    if (!pd) pd = this.peerData[peer] = this.peerDataDefault()
    if (value) {
      if (value == '+')
        value = pd.value + TimerIncrement
      else if (value == '-')
        value = pd.value - TimerIncrement
      pd.peerTimeout = value
    }
    return pd.peerTimeout
  }
  
  query(command, data, cb) {		//---- Communicate with app regarding keys, tickets
    if (!this.queryCB) return false
    this.queryCB(command, data, cb)
    return true
  }

  end(peer) {		//---- Close any socket with the specified peer
    let pc = this.connections.find(peer, (v,o)=>(v == o.peer))
    if (pc) return pc.end()

    for (let c of this.connections.set) {	//And close any open connections we may have
      if (!peer || peer == c.peer) c.end()
    }
  }

  close() {		//---- Close server and all connections
    this.log.debug('Closing server on port:', this.port)
    this.server.close()				//Quit listening for incoming connections

    this.end()				//And close any open connections we may have
  }
  
  forget(pc) {		//---- Remove peer controller from list of open connections
//this.log.debug('Forget:', this.connections.size(), pc.peer)
//for (let p of this.connections.set) {this.log.debug(' p:', p.peer, p.state)}
    this.connections.delete(pc)
//this.log.debug('  length now:', this.connections.size())
  }

  send(peer, messageObj, successCB, failureCB) {	//---- Try to send to a peer, who may or may not be connected
this.log.debug('Peercomm send to:', peer)
    if (peer == this.peer) {				//This is local traffic
      setTimeout(() => {
        this.messageCB(this.peer, messageObj)		//Pass it back to ourselves as the next event
        if (successCB) successCB()
      })
      return
    }

    let pc = this.connections.find(peer, (v,o)=>(v==o.peer))		//Find any existing connection
    if (!pc) {						//Build a connection if necessary
this.log.debug('Creating control object for new peer:', peer)
      pc = new PeerConnection(peer, null, this)
      if (pc.send(messageObj, successCB, failureCB))	//And then request it to send
        this.connections.add(pc)			//Register in our collection

    } else {						//Already have a peer connection object
this.log.debug('Found existing control object for peer:', peer)
      pc.send(messageObj, successCB, failureCB)
    }
  }

}		//class PeerSocket

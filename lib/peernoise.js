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
//- Add try/catch at strategic calls to avoid server potentially crashing
//- Implement (or remove) queue functionality
//-   If we get a message for a connection that is pending, queue the message
//-   For K connect packets, we really shouldn't send the message until the connection has settled
//- Test timeouts
//- Make timeouts adaptive?  The more we connect to a certain address, the longer the timeouts
//- Pare down the amount of debug comments
//- See other Fixme's below
//- 
const Os = require('os')
const Net = require('net')
const Url = require('url')
const { Log } = require('wyclif')		//Default logging
const ObjectSet = require('./objectset')
const NoiseWrap = require('./noisewrap.js')	//Generic Noise routines
const { Address6 } = require('ip-address')
const Frame = require('frame-stream')		//Delimit packets over TCP
const DefaultTimeout = 60000			//Keep connections open for 1 minute
const TimeoutIncrement = 30000
const DefaultPort = 65430
const Encoding = 'utf8'

class PeerConnection {		//One of these for each new connection with a peer
  constructor(chad, socket, manager) {
    this.manager = manager			//parent object
    this.log = manager.log || (()=>null)
//    this.queue = []				//pending messages; Fixme: do we need this?
    this.state = 'none'				//No validated connecton yet
    this.raw = !('secretKey' in manager.keys)
    this.n = new NoiseWrap({log: this.log, raw: this.raw})
    
    if (chad && !socket) {			//The manager must initiate the connection using this.send()
      this.setPeerInfo(chad)
this.log.debug('New PC; peer:', chad, this.state, 'Raw:', this.raw)
      this.initiator = true			//We can send:I,N,K,T; receive:A,T

    } else if (!chad && socket) {		//Unidentified peer connected to us as a client
this.log.debug('New PC; addr:', socket.remoteAddress, 'Raw:', this.raw)
      let s = this.initFraming(socket)		//Process stream as complete messages
      this.resetTimeout(manager.timeout)	//We are responsible for disconnect timeouts
      this.initiator = false			//We can send:A,T; receive:I,N,K,T
      this.peerKey = null			//We don't know who it is yet

      s.on('data', d=>this.fromInitiator(d))	//When data comes in
      s.on('error', e => {this.log.error('Socket error:', this.agent, e.message)})
      s.on('end', () => this.socketEnd())
    }		//if
  }		//constructor

  //---- Set remote peer data
  setPeerInfo({agent, host, port, key}) {
    this.peerAgent = agent
    this.peerHost = host
    this.peerPort = port
    this.peerKey = key || Buffer.from(agent,'base64url')	//explicit key or decode from agent name
  }

  //---- Interpret an incoming message as JSON content
  packetParse(message) {
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

  //---- Parse NPF packet if it matches a specified header
  eatNoise(packet, initiator, validHeaders, cb) {
    let header = packet.slice(0,1).toString()		//Point to the header character
      , data = packet.slice(1)				//Data in the rest of the packet
      , receiveBuf = Buffer.alloc(packet.byteLength)	//Plaintext should be shorter than encrypted
        
    if (!validHeaders.includes(header)) return false	//Ignore unexpected packet types
this.log.trace('eatNoise:', header, validHeaders)
    if (initiator !== null) {				//Initiator true or false: initiate noise state
      let hs1 = "IKN".includes(header) ? header : 'K'	//Expecting only I,K,N packets
        , handshake = hs1 + (hs1 == 'N' ? '' : 'K')	//Build handshake IK, KK, N
        , peerKey = hs1 == 'K' ? this.peerKey : null
this.log.trace('preNoise:', hs1, handshake, this.peerKey, peerKey)
      this.noiseState = this.n.initialize(handshake, initiator, this.manager.keys, peerKey)
    }
    this.split = this.n.readMessage(this.noiseState, data, receiveBuf)
this.log.trace('postNoise:', this.noiseState, this.n.readMessage.bytes, receiveBuf.slice(0,this.n.readBytes).toString(), 'split:', this.split)
    if (cb) cb(header, this.packetParse(receiveBuf.slice(0, this.n.readBytes)))
    return true
  }

  //---- Create and send NPF acknowledge packet
  spewNoise(header = 'A', message = '', state = this.noiseState) {
    let messageBuf = Buffer.from(message)
      , packetBuf = Buffer.alloc(messageBuf.byteLength + this.n.BufferAdd)
      , noiseBuf = packetBuf.slice(1)		//Write noise data after header
    packetBuf.write(header)
    this.split = this.n.writeMessage(state, messageBuf, noiseBuf)
    this.encode.write(packetBuf.slice(0,this.n.writeBytes + 1))
this.log.trace('Spew:', header, packetBuf.slice(0,this.n.writeBytes).toString('hex'), 'split:', !!this.split)
  }

  //---- Set alarm to close channel if not used within time
  resetTimeout(defaultTimeout) {
    let time = this.manager.peerTimeout(this.agent, defaultTimeout) || DefaultTimeout
    if (this.timer) clearTimeout(this.timer)		//Clear any timeout timer
    this.timer = setTimeout(() => {			//And set a new one
this.log.trace("Peernoise timeout:", this.agent)
      this.end()
    }, time)
  }

  //---- Handle incoming data (I,N,K,T) from a client
  fromInitiator(packet) {
    this.resetTimeout()
  
    if (this.state == 'open') {			//Established connection
this.log.trace('Got packet on open channel:', packet)
      this.decrypt(packet)			//Will only accept T packets

    } else if (this.state == 'none') {		//First packet, should be I or N
      this.eatNoise(packet, false, ['I','N'], (header, data) => {
this.log.trace('Got first packet:', header, data)
        if (header == 'N') {
          if (!data) return
          this.setPeerInfo({agent:data})		//Data better be a valid agent name
          this.state = 'id'
this.log.trace('Got N packet:', data, 'peerKey:', this.peerKey)
          
        } else if (header == 'I') {
this.log.trace('Got I packet:', data, data.ticket)
          if (!data || !data.ticket || !data.from) return
          this.state = 'ticket'
          this.setPeerInfo(data.from)		//Packet better be a valid from address
          this.manager.query('ticket', data.ticket, () => {	//Have app validate ticket
            this.spewNoise()			//Acknowledge completes noise connection
            this.state = 'open'
this.log.trace('PK:', JSON.stringify(this.peerKey), JSON.stringify(this.noiseState.rs))
            this.peerKey = this.n.keyCheck(this.noiseState, this.peerKey)	//Verify connecting key with declared key
            this.n.destroy(this.noiseState)
            if (data && Object.keys(data).length >= 1)	//Process message if any
              this.manager.messageCB(this,data)
          })	//query
        }	//if header
      })	//eatNoise()

    } else if (this.state == 'id') {		//expecting a K packet
this.log.trace('Packet on pending channel:', packet, 'peerKey:', this.peerKey)

      this.eatNoise(packet, false, ['K'], (header, data) => {
this.log.trace('Packet:', header, data, 'peerKey:', this.peerKey)
        this.state = 'open'
        this.spewNoise()			//Acknowledge completes noise connection
        if (data && Object.keys(data).length >= 1)	//Process message if any
          this.manager.messageCB(this,data)
      })
      
    } else {		//state = request or ticket
this.log.error('Unexpected packet:', header, data)
    }
  }		//fromInitiator

  //---- Handle incoming data (A,T) from a server
  fromResponder(packet) {
this.log.trace('Server message:', this.state, packet.slice(0,1).toString(), packet.toString('hex'))

    if (this.state == 'open') {			//Should get T only
      this.decrypt(packet)

    } else if (this.state == 'pending') {	//Should get A only
      this.eatNoise(packet, null, ['A'], (header, data) => {
this.log.trace('Ate packet:', header, data)
        if (header == 'A') {			//Got acknowledge
          this.state = 'open'			//Channel now open
          this.n.destroy(this.noiseState)
          if (data && Object.keys(data).length <= 1)	//If any data came along, process it
            this.manager.messageCB(this, data)
        }
      })
    }

  }	//fromResponder

  //---- Get remote IP address socket is connected to
  peerAddress() {
this.log.trace("Peer address:", this.agent)
    if (!this.fromAddress) {
      if (this.socket.remoteFamily == 'IPv6') {
        this.fromAddr = new Address6(this.socket.remoteAddress).correctForm()
      } else {
        this.fromAddr = Address6.fromAddress4(this.socket.remoteAddress).correctForm()
      }
    }
    return this.fromAddr
  }	//fromAddress
  
  //---- Close this connection
  end() {
//this.log.debug("Ending peer connection:", this.agent, this.host, this.port)
    if (this.timer) clearTimeout(this.timer)
    if (this.socket) this.socket.end()
    this.manager.forget(this)
  }
  
  //---- Handle unexpected end event
  socketEnd() {
    this.log.warn('Socket disconnected:', this.agent)
    this.socket = null
    this.end()
  }

  //---- Begin a noise connection
  initiate(messageObj, successCB, failureCB) {
    let {target, action, ticket} = messageObj
      , hs1 = 'K'
this.log.debug('Initializing noise:', this.manager.keys.publicKey, this.peerKey, messageObj)
    if (target == 'tally' && action == 'ticket' && ticket) {
      hs1 = 'I'					//First character of handshake
    } else {
      let header = 'N'				//First send an N record with node ID
        , ns = this.n.initialize(header, true, this.manager.key, this.peerKey)
      this.spewNoise(header, JSON.stringify(this.manager.agent), ns)	//Our ID
      this.n.destroy(ns)
    }

    if (!messageObj.from) messageObj.from = {}	//Assure valid from-address on packet
    Object.assign(messageObj.from, this.manager.chad)	//Guaranty correct agent,port info

    let messageBuf = Buffer.from(JSON.stringify(messageObj))
      , packetBuf = Buffer.alloc(messageBuf.byteLength + this.n.BufferAdd)
      , noiseBuf = packetBuf.slice(1)		//Noise starts after header character

    this.noiseState = this.n.initialize(hs1 + 'K', this.initiator = true, this.manager.keys, this.peerKey)
    this.split = this.n.writeMessage(this.noiseState, messageBuf, noiseBuf)
this.log.trace('Noise generates split:', typeof this.split)

    packetBuf.write(hs1)				//Packet header
this.log.trace('Writing bytes:', this.n.writeBytes, packetBuf.toString())
    this.encode.write(packetBuf.slice(0, this.n.writeBytes + 1), null, successCB)
    this.state = 'pending'
  }
  
  //---- Decrypt, parse and process a T message
  decrypt(packet) {
    let header = packet.slice(0,1).toString()
      , messageBuf = packet.slice(1)
      , decryptBuf = Buffer.alloc(packet.byteLength)	//Plaintext should be shorter than this

    if (header != 'T') return			//Ignore invalid packets
this.log.trace('Got packet:', header, messageBuf.toString('hex'), messageBuf.byteLength)
    if (!this.raw && (!this.split || !this.split.rx)) {
      this.log.error('No decryption key found')
    } else {
      this.n.decrypt(this.split, decryptBuf, messageBuf)
this.log.trace('Decrypted:', header, decryptBuf.toString())
      let messageObj = this.packetParse(decryptBuf.slice(0, this.n.decryptBytes))
      this.manager.messageCB(this, messageObj)
    }
  }

  //---- Encrypt and send a message
  encrypt(messageObj, successCB, failureCB) {
    let message = Buffer.from(JSON.stringify(messageObj))
      , packetBuf = Buffer.alloc(message.byteLength + this.n.BufferAdd)
      , encryptBuf = packetBuf.slice(1)
    if (!this.raw && (!this.split || !this.split.tx)) {
      this.log.error('No encryption key found')
      if (failureCB) failureCB()
    } else {
      this.n.encrypt(this.split, encryptBuf, message)
      let sendBuf = packetBuf.slice(0, this.n.encryptBytes + 1)
      sendBuf.write('T')
this.log.trace('Write:', sendBuf.toString(this.raw ? 'utf-8' : 'hex'))
      this.encode.write(sendBuf, Encoding, successCB)
    }
  }

  //---- Send a message, opening the connection first if necessary
  send(messageObj, successCB, failureCB) {
this.log.debug('In PC send; state:', this.state, messageObj)
    if (this.state == 'open') {			//Channel is already open, can just write message
      this.encrypt(messageObj, successCB, failureCB)
      return true
    }
//Fixme: need this?
//    this.queue.push({messageObj, successCB, failureCB})	//Save message until channel opens

    if (this.state != 'none') {
//Fixme: should I set a timer in case opening doesn't resolve?
//Fixme: What will happen to this message
this.log.debug('Found pending state:', this.state)

    } else {				//state == none; Need to initiate a noise connection
      if (!this.peerHost || !this.peerPort) {
        if (failureCB) failureCB()
        return false
      }
      let client = Net.connect(this.peerPort, this.peerHost, () => {	//Connect to peer as client
        let s = this.initFraming(client)	//Process stream as complete messages

this.log.debug('Connected as client to:', this.peerAgent)
        s.on('data', d=>this.fromResponder(d))	//When data comes in
        s.on('error', e => {this.log.error('Socket error:', this.agent, e.message)})
        s.on('end', () => this.socketEnd())

        this.initiate(messageObj, successCB, failureCB)
      })	//connect
    }		//if
    return true
  }		//send

  //---- Configure socket to handle complete, delimited messages
  initFraming(socket) {
    let s = socket.pipe(Frame.decode())	//Process stream as complete messages
    this.encode = Frame.encode()		//Write to encode method to frame our messages
    this.encode.pipe(socket)
    this.socket = socket
    return s
  }

}		//peerConnection

//---- Connection server side, listener/responder
module.exports = class {
  constructor(config, messageCB) {
    this.keys = config.keys || {}
    this.host = config.host || Os.hostname()		//Our address for other peers
    this.port = config.port || DefaultPort		//Port we listen to
    this.agent = config.agent || Buffer.from(this.keys.publicKey).toString('base64url')
    this.chad = {agent:this.agent, host:this.host, port:this.port}	//Local CHIP address
    this.messageCB = messageCB				//Call this when we receive data
    this.timeout = config.timeout || DefaultTimeout
    this.queryCB = config.queryCB || (()=>null)	//Call to query for keys, tokens, tallies
    this.connections = new ObjectSet()			//Keep list of current peer sockets
    this.log = config.log || Log('peercomm')
    this.log.debug('Peer noise server listening on port:', this.port)
    this.peerData = {}					//Cache info about peers
    this.peerDataDefault = () => ({timeout: this.timeout})

    this.server = Net.createServer(sock => {		//Initialize server to receive connections from peer clients
this.log.debug('Peer initiated connection on:', this.port, ' from:', sock.remoteAddress)
      let pc = new PeerConnection(null, sock, this)
      this.connections.add(pc)				//Register in our collection
    }).listen(this.port)
  }	//constructor()

  //---- Get/set cached value for peer adaptive timeout value
  peerTimeout(agent, value) {
    let pd = this.peerData[agent]
    if (!pd) pd = this.peerData[agent] = this.peerDataDefault()
    if (value) {
      if (value == '+')
        value = pd.value + TimerIncrement
      else if (value == '-')
        value = pd.value - TimerIncrement
      pd.peerTimeout = value
    }
    return pd.peerTimeout
  }
  
  //---- Communicate with app regarding keys, tickets
  query(command, data, cb) {
    if (!this.queryCB) return false
    this.queryCB(command, data, cb)
    return true
  }

  //---- Close any socket with the specified peer
  end(peer) {
    let pc = this.connections.find(peer, (v,o)=>(v == o.peer))
    if (pc) return pc.end()

    for (let c of this.connections.set) {	//And close any open connections we may have
      if (!peer || peer == c.peer) c.end()
    }
  }

  //---- Close server and all connections
  close() {
    this.log.debug('Closing server on port:', this.port)
    this.server.close()				//Quit listening for incoming connections

    this.end()				//And close any open connections we may have
  }

  //---- Remove peer controller from list of open connections
  forget(pc) {
    this.connections.delete(pc)
  }

  //---- Try to send to a peer, who may or may not be connected
  send(messageObj, successCB, failureCB) {
    let {to} = messageObj
      , {agent, host, port} = to
this.log.debug('Peercomm send to:', agent, host, port)
    if (!agent || !host || !port) return failureCB()

    if (agent == this.agent) {				//This is local traffic
      setTimeout(() => {
        this.messageCB(this.agent, messageObj)		//Pass it back to ourselves as the next event
        if (successCB) successCB()
      })
      return
    }

    let pc = this.connections.find(agent, (v,o)=>(v==o.peerAgent))	//Find any existing connection
    if (!pc) {						//Build a connection if necessary
this.log.debug('Creating control object for new peer agent:', agent)
      pc = new PeerConnection(to, null, this)
      if (pc.send(messageObj, successCB, failureCB))	//And then request it to send
        this.connections.add(pc)			//Register in our collection

    } else {						//Already have a peer connection object
this.log.debug('Found existing control object for peer:', agent)
      pc.send(messageObj, successCB, failureCB)
    }
  }

}		//class PeerSocket

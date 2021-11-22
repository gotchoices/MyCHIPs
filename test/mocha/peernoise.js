//Test peer-to-peer communications channel
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//X- Test connecting without ticket
//X- Peercomm module can cache ID's of peers to avoid repeated queries of DB on reconnection
//- 

const assert = require('assert');
const Noise = require('noise-protocol')
const { Address6 } = require('ip-address')
const PeerNoise = require('../../lib/peernoise')
const { Log } = require('../settings')

const initiatorPort = 55551
const responderPort = 55552
const hostname = 'localhost'
const initiatorAt = hostname + ':' + initiatorPort
const responderAt = hostname + ':' + responderPort
var log = Log('testPeercomm')
var logI = Log('testPeercommI')		//Enable separate logging for each end
var logR = Log('testPeercommR')
var message1 = "This is a test message."
var message2 = "I hear you!"
var message3 = "Can I hear myself?"
var token1 = "My Custom Token"

// Regular token-based connection
// ----------------------------------------------------------------------------
var Suite1 = function({initiatorConfig, initiatorCB, initiatorTicket, responderConfig, responderCB}) {
  var initiator, responder;

  before('Launch initiator and responder', function() {
    responderConfig.queryCB = function(req, data, cb) {
logR.debug("Responder got query request:", req, data)
      if (req == 'ticket') {
        assert.equal(data.token, token1)	//Correct token being returned
        cb()					//Always consider valid
      } else if (req == 'store') {
        let { peer, key } = data
//logR.debug("I Key:", initiatorConfig.key.publicKey.toString('hex'))
//logR.debug("N Key:", key.toString('hex'))
        assert.equal(peer, initiatorAt)
        assert.deepEqual(key, initiatorConfig.key.publicKey)		//Key we got back was what was sent
      }
    }
    initiatorConfig.queryCB = function(req, data, cb) {
logI.debug("Initiator got query request:", req, data)
      assert.equal(data, responderAt)		//Asking for responder
      if (req == 'key') cb(responderConfig.key.publicKey)
      return true
    }
    responder = new PeerNoise(responderConfig, (c,o) => responderCB(c,o))
    initiator = new PeerNoise(initiatorConfig, (c,o) => initiatorCB(c,o))
  })

  it("Send a ticket-connect request from initiator to responder", function(done) {
    responderCB = function(connection, obj) {		//when a message comes in
      connection.send(obj)				//loop it back to the sender
    }
    initiatorCB = function(connection, obj) {
      assert.equal(obj.text, message1)			//Got the same message we sent
      done()
    }
    initiator.send(responderAt, {	//Send the test message
      text:	message1,
      ticket:	initiatorTicket
    }, null, e => done(e))
  })

  it("Send from responder to initiator", function(done) {
    initiatorCB = function(connection, obj) {
      assert.equal(obj.text, message2)			//Got the same message we sent
      done()
    }
    responder.send(initiatorAt, {text: message2}, null, e=>done(e))
  })

  it("Send from initiator to initiator", function(done) {
    initiatorCB = function(connection, obj) {
      assert.equal(obj.text, message3)			//Got the same message we sent
      done()
    }
    initiator.send(initiatorAt, {text: message3}, null, e=>done(e))
  })

  it("Send from responder to a bad address should fail", function(done) {
    responder.send('bad_address', {text: message2}, null, function() {
      done()
    })
  })

  it("Can fetch remote connection address", function() {
    responderCB = function(connection, obj) {
      let pa = connection.peerAddress()
        , aa = new Address6(connection.socket.remoteAddress).correctForm()
logR.debug('Address:', connection.peer, pa)
      assert.equal(obj.text, message1)
      assert.ok(!!pa)
      assert.equal(pa, aa)
    }
    initiator.send(responderAt, {text: message1}, null, e=>{
      assert.fail('Send invoked failure callback')
    })
  })

  it("Can close a connection and resend", function(done) {
    responderCB = function(connection, obj) {
logR.debug('RespCB:', connection, obj)
      assert.equal(obj.text, message2)
      done()
    }
    
    initiator.end(responderAt)
    setTimeout(() => {
      initiator.send(responderAt, {text: message2}, null, e=>{
        assert.fail('Send invoked failure callback')
      })
    }, 25)
  })

  after('Clean up peer objects', function() {
    initiator.close()
    responder.close()
  })
}

// Reconnection based on previously shared keys
// ----------------------------------------------------------------------------
var Suite2 = function({initiatorConfig, initiatorCB, initiatorTicket, responderConfig, responderCB}) {
  var initiator, responder;

  before('Launch servers', function() {
    responderConfig.queryCB = function(req, data, cb) {
logR.debug("Responder got query request:", req, data)
      assert.equal(data, initiatorAt)		//Asking for initiator
      if (req == 'key') cb(initiatorConfig.key.publicKey)
      return true
    }
    initiatorConfig.queryCB = function(req, data, cb) {
logI.debug("Initiator got query request:", req, data)
      assert.equal(data, responderAt)		//Asking for responder
      if (req == 'key') cb(responderConfig.key.publicKey)
      return true
    }
    responder = new PeerNoise(responderConfig, (c,o) => responderCB(c,o))
    initiator = new PeerNoise(initiatorConfig, (c,o) => initiatorCB(c,o))
  })

  it("Send a key-connect request from initiator to responder", function(done) {
    responderCB = function(connection, obj) {		//when a message comes in
      connection.send(obj)				//loop it back to the sender
    }
    initiatorCB = function(connection, obj) {
      assert.equal(obj.text, message1)			//Got the same message we sent
      done()
    }
    initiator.send(responderAt, {	//Send the test message
      text:	message1,
    }, null, e => done(e))
  })

  after('Clean up peer objects', function() {
    initiator.close()
    responder.close()
  })
}

// Main
// ----------------------------------------------------------------------------
describe("Peernoise module testing", function() {

  let configGenerator = (raw) => {		//Build a configuration block for the test
    let initiatorKey = Noise.keygen()
      , responderKey = Noise.keygen()
    if (raw) {					//No private key triggers unencrypted mode
      delete initiatorKey.secretKey
      delete responderKey.secretKey
    }
    return {
      initiatorConfig: {
        log:	logI,
        host:	hostname,
        port:	initiatorPort,
        key:	initiatorKey
      },
      responderConfig: {
          log:	logR,
          host:	hostname,
          port:	responderPort,
          key:	responderKey
      },
      initiatorCB:null,
      responderCB:null,
      initiatorTicket: {
          token:	token1,
          key:		responderKey.publicKey,
      }
    }
  }
    , configN = configGenerator()		//For noise-based connection
    , configR = configGenerator(true)		//For unencrypted connection

  describe("P2p Noise Protocol Suite 1", function() {Suite1(configN)})
  describe("P2p Noise Protocol Suite 2", function() {Suite2(configR)})

  describe("P2P Raw Mode Suite 1", function() {Suite1(configR)})
  describe("P2p Raw Mode Suite 2", function() {Suite2(configR)})
})

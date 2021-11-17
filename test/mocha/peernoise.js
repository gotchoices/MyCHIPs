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
const responderPort = 55551
const initiatorPort = 55552
const hostname = 'localhost'
const initiatorAt = "localhost" + ':' + initiatorPort
const responderAt = "localhost" + ':' + responderPort
var initiatorKey = Noise.keygen()
var responderKey = Noise.keygen()
var log = Log('testPeercomm')
var logI = Log('testPeercommI')		//Enable separate logging for each end
var logR = Log('testPeercommR')
var message1 = "This is a test message."
var message2 = "I hear you!"
var message3 = "Can I hear myself?"
var token1 = "My Custom Token"
var initiatorTicket = {		//Allows connection to responder
  token:	token1,
  key:		responderKey.publicKey,
}
var initiatorConfig = {
  log:		logI,
  address:	hostname,
  port:		initiatorPort,
  siteKey:	initiatorKey,
}
var responderConfig = {
  log:		logR,
  address:	hostname,
  port:		responderPort,
  siteKey:	responderKey,
}
var initiatorCB, responderCB
//let pK = initiatorKey.publicKey
//  , pKb6 = Buffer.from(pK).toString('base64').replace(/=+$/,'').replace('+','-').replace('/','_')
//log.debug('Initiator key:', pKb6)

describe("Peer to peer noise protocol communications test 1", function() {
  var initiator, responder;

  before('Launch initiator and responder', function() {
    responderConfig.queryCB = function(req, data, cb) {
logR.debug("Responder got query request:", req, data)
      if (req == 'ticket') {
        assert.equal(data.token, token1)	//Correct token being returned
        cb()					//Always consider valid
      } else if (req == 'store') {
        let { peer, key } = data
//logR.debug("I Key:", initiatorKey.publicKey.toString('hex'))
//logR.debug("N Key:", key.toString('hex'))
        assert.equal(peer, initiatorAt)
        assert.deepEqual(key, initiatorKey.publicKey)		//Key we got back was what was sent
      }
    }
    initiatorConfig.queryCB = function(req, data, cb) {
logI.debug("Initiator got query request:", req, data)
      assert.equal(data, responderAt)		//Asking for responder
      if (req == 'key') cb(responderKey.publicKey)
      return true
    }
    responder = new PeerNoise(responderConfig, (c,o) => responderCB(c,o))
    initiator = new PeerNoise(initiatorConfig, (c,o) => initiatorCB(c,o))
  })

  it("Send a ticket-connect request from initiator to responder", function(done) {
    responderCB = function(connection, obj) {	//when a message comes in
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
});

describe("Peer to peer noise protocol communications test 2", function() {
  var initiator, responder;

  before('Launch servers', function() {
    responderConfig.queryCB = function(req, data, cb) {
logR.debug("Responder got query request:", req, data)
      assert.equal(data, initiatorAt)		//Asking for initiator
      if (req == 'key') cb(initiatorKey.publicKey)
      return true
    }
    initiatorConfig.queryCB = function(req, data, cb) {
logI.debug("Initiator got query request:", req, data)
      assert.equal(data, responderAt)		//Asking for responder
      if (req == 'key') cb(responderKey.publicKey)
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
})

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
const { testLog } = require('./common')

const initPort = 55551
const respPort = 55552
const hostname = 'localhost'
//const initAt = hostname + ':' + initPort
//const respAt = hostname + ':' + respPort
var log = testLog(__filename)
var logI = testLog(__filename + '-I')		//Enable separate logging for each end
var logR = testLog(__filename + '-R')
var message1 = "This is a test message."
var message2 = "I hear you!"
var message3 = "Can I hear myself?"
var token1 = "My Custom Token"

// Regular token-based connection
// ----------------------------------------------------------------------------
var Suite1 = function({initConfig, initCB, initCHAD, initTicket, respConfig, respCB, respCHAD}) {
  var initiator, responder;

  before('Launch initiator and responder', function() {
    respConfig.queryCB = function(req, data, cb) {
log.debug("Responder got query request:", req, data)
      if (req == 'ticket') {
        assert.equal(data.token, token1)	//Correct token being returned
        cb()					//Always consider valid
      }
    }
    initConfig.queryCB = function(req, data, cb) {
logI.debug("Initiator got query request:", req, data)
    }
    responder = new PeerNoise(respConfig, (c,o) => respCB(c,o))
    initiator = new PeerNoise(initConfig, (c,o) => initCB(c,o))
  })

  it("Send a ticket-connect request from initiator to responder", function(done) {
    respCB = function(connection, obj) {		//when a message comes in
      connection.send(obj)				//loop it back to the sender
    }
    initCB = function(connection, obj) {
      assert.equal(obj.text, message1)			//Got the same message we sent
      done()
    }

    initiator.send({		//Send the test message
      to:	respCHAD,
      ticket:	initTicket,
      text:	message1,
    }, null, e => done(e))
  })

  it("Send from responder to initiator on existing connection", function(done) {
    let dc = 2, _done = () => {if (!--dc) done()}	//2 _done's to be done
    initCB = function(connection, obj) {
      assert.equal(obj.text, message2)			//Got the same message we sent
      assert.equal(responder.connections.size(), 1)	//Should reuse existing connection
      _done()
    }
    responder.send({to: initCHAD, text: message2}, ()=>_done(), e=>done(e))
  })

  it("Send from initiator to initiator", function(done) {
    let dc = 2, _done = () => {if (!--dc) done()}
    initCB = function(connection, obj) {
      assert.equal(obj.text, message3)			//Got the same message we sent
      _done()
    }
    initiator.send({to: initCHAD, text: message3}, ()=>_done(), e=>done(e))
  })

  it("Send to a bad address calls failure CB", function(done) {
    responder.send({to:{agent:'bad_agent'}, text: message2}, null, function() {
      done()
    })
  })

  it("Can fetch remote connection address", function() {
    respCB = function(connection, obj) {
      let pa = connection.peerAddress()
        , aa = new Address6(connection.socket.remoteAddress).correctForm()
logR.debug('Address:', connection.peer, pa)
      assert.equal(obj.text, message1)
      assert.ok(!!pa)
      assert.equal(pa, aa)
    }
    initiator.send({to: respCHAD, text: message1}, null, e=>{
      assert.fail('Send invoked failure callback')
    })
  })

  it("Can close a connection and resend", function(done) {
    respCB = function(connection, obj) {
logR.debug('RespCB:', connection, obj)
      assert.equal(obj.text, message2)
      done()
    }
    
    initiator.end(respCHAD.agent)
    setTimeout(() => {
      initiator.send({to: respCHAD, text: message2}, null, e=>{
        assert.fail('Send invoked failure callback')
      })
    }, 25)
  })

/* */
  after('Clean up peer objects', function() {
    initiator.close()
    responder.close()
  })
}

// Reconnection based on previously shared keys
// ----------------------------------------------------------------------------
var Suite2 = function({initConfig, initCB, initCHAD, initTicket, respConfig, respCB, respCHAD}) {
  var initiator, responder;

  before('Launch servers', function() {
    respConfig.queryCB = function(req, data, cb) {
logR.debug("Responder got query request:", req, data)
//      assert.equal(data, initAt)		//Asking for initiator
      if (req == 'key') cb(initConfig.keys.publicKey)
      return true
    }
    initConfig.queryCB = function(req, data, cb) {
logI.debug("Initiator got query request:", req, data)
//      assert.equal(data, respAt)		//Asking for responder
      if (req == 'key') cb(respConfig.keys.publicKey)
      return true
    }
    responder = new PeerNoise(respConfig, (c,o) => respCB(c,o))
    initiator = new PeerNoise(initConfig, (c,o) => initCB(c,o))
  })

  it("Send a key-connect request from initiator to responder", function(done) {
    respCB = function(connection, obj) {		//when a message comes in
      connection.send(obj)				//loop it back to the sender
    }
    initCB = function(connection, obj) {
      assert.equal(obj.text, message1)			//Got the same message we sent
      done()
    }
    initiator.send({	//Send the test message
      to: respCHAD,
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
    let initKeys = Noise.keygen()
      , respKeys = Noise.keygen()
      , initAgent = Buffer.from(initKeys.publicKey).toString('base64url')
      , respAgent = Buffer.from(respKeys.publicKey).toString('base64url')
    if (raw) {					//No private key triggers unencrypted mode
      delete initKeys.secretKey
      delete respKeys.secretKey
    }
    return {
      initConfig: {
        log:	logI,
        host:	hostname,
        port:	initPort,
        keys:	initKeys
      },
      respConfig: {
        log:	logR,
        host:	hostname,
        port:	respPort,
        keys:	respKeys
      },
      initCB:null,
      respCB:null,
      initTicket: {
        token:	token1,
//        key:	respKeys.publicKey,
      },
      initCHAD: {
        agent: initAgent,
        host: hostname,
        port: initPort
      },
      respCHAD: {
        agent: respAgent,
        host: hostname,
        port: respPort
      }
    }
  }
  let configN = configGenerator()		//For noise-based connection
    , configR = configGenerator(true)		//For unencrypted connection

  describe("P2p Noise Protocol Suite 1", function() {Suite1(configN)})
  describe("P2p Noise Protocol Suite 2", function() {Suite2(configR)})

  describe("P2P Raw Mode Suite 1", function() {Suite1(configR)})
  describe("P2p Raw Mode Suite 2", function() {Suite2(configR)})
})

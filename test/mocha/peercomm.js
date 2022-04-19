//Test peer-to-peer communications channel
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
const port1 = 55551
const port2 = 55552
const assert = require("assert");
const PeerComm = require("../../lib/peercomm")
const { testLog } = require('./common')
const serv1 = "localhost:" + port1
var log1 = testLog(__filename + '-1')		//Enable separate logging for each end
var log2 = testLog(__filename + '-2')
const config1 = {port: port1, log: log1}
const config2 = {port: port2, log: log2}
var callback1, callback2
var msg1 = "This is a test message."
var msg2 = "Hello there!"

describe("Peer to peer raw communications test", function() {
  var server1, server2;

  before('Launch a server', function() {
    server1 = new PeerComm(config1, (c,o) => callback1(c,o))
    server2 = new PeerComm(config2, (c,o) => callback2(c,o))
    
    callback1 = function(serv, obj) {
      server1.send(serv, obj)		//loop the message back
    }
  })

  it("Sends an object from one socket to another", function(done) {
    callback2 = function(serv, obj) {
      assert.equal(obj.txt, msg1)	//Got the same message we sent
      done()
    }
    server2.send(serv1, {txt: msg1})	//Send a test message
  })

  it("Sends second object", function(done) {
    callback2 = function(serv, obj) {
      assert.equal(obj.txt, msg2)	//Got the same message we sent
      done()
    }
    server2.send(serv1, {txt: msg2})	//Send a test message
  })

  it("Test local loopback", function(done) {
    callback1 = function(serv, obj) {
      assert.equal(obj.txt, msg1)	//Got the same message we sent
      done()
    }
    server1.send(serv1, {txt: msg1})	//Send a test message
  })
/* */
  after('Clean up servers', function() {
    server1.close()
    server2.close()
  })
});

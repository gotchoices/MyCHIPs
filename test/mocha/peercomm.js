//Test peer-to-peer communications channel
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
const port1 = 55551
const port2 = 55552
const assert = require("assert");
const PeerComm = require("../../lib/peercomm")
const serv1 = "localhost:" + port1
var msg1 = "This is a test message."

describe("Peer to peer communications test", function() {
  var server1, server2;

  before('Launch a server', function() {
    server1 = new PeerComm(port1, null, function(serv, obj) {
      server1.send(serv, obj)		//loop the message back
    })
  })

  it("Sends an object from one socket to another", function(done) {
    server2 = new PeerComm(port2, null, function(serv, obj, sock) {
      assert.equal(obj.txt, msg1)	//Got the same message we sent
      done()
    })
    server2.send(serv1, {txt: msg1})	//Send a test message
  })

  after('Clean up servers', function() {
    server1.close()
    server2.close()
  })
});

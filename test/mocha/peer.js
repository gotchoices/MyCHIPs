//Test tallys and chits between peers
//TODO:
//X- Separate test tag to create testing database with example data, users, etc.
//X- Separate test tag to destroy testing database (will do manually for now)
//X- Require database wyseman module, specifying the test database
//- Script for loading the database with sample test data (as a single sql file)
//- Identify two sample users
//- Delete any tallies between these two users
//- Create an initial tally invitation
//- Check the state of the database
//- Create test for each pathway of the flow chart
//- Check the state of the database after each stage
//- Create similar testing for chit flowchart
//- 

const port1 = 65431
const port2 = 65432
const host1 = "server1"
const host2 = "server2"
const assert = require("assert");
const PeerCont = require("../../lib/peer")
const DatabaseName = "mychipsTestDB"
var log = require('../../lib/logger')('testpeer')
var { dbClient } = require("wyseman")
const dbConfig = {
  database: DatabaseName,
  listen: "DummyChannel",		//Force immediate connection to our DB
  logger: log,
  schema: __dirname + "/../../lib/schema.sql"
}

describe.skip("Peer to peer tallies", function() {
  var server1, server2
  var db

  before('Connect to (or create) test catabase', function(done) {
    db = new dbClient(dbConfig, (chan, data) => {
      log.trace("Notify from channel:", chan, "data:", data)
    }, ()=>{
      log.trace("Connected")
      done()
    })
  })

  before('Launch two peer servers', function() {
    server1 = new PeerCont(port1, host1, dbConfig)
//    server2 = new PeerCont(port2, host2, dbConfig)
  })

  it("Propose tally", function(done) {
    db.query("select count(*) from mychips.users_v", null, (err, res) => {
console.log("Err:", err, "Res:", res)
      assert.equal(true,true)
      done()
    })
  })

  after('Disconnect from test database', function(done) {
//    server2.close(serv1)
    db.disconnect
    done()
  })
});

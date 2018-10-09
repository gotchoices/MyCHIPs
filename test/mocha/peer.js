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

const assert = require("assert");
const PeerCont = require("../../lib/peer")
const DatabaseName = require('../database')
const MachineIP = "192.168.57.101"
const Uport=43210
const Pport0=65430
const Pport1=65431
const Host0 = "server0"
const Host1 = "server1"
var log = require('../../lib/logger')('testpeer')
var { dbClient } = require("wyseman")

//Initialize users
const sqlUserInit = `begin; \n\
  update mychips.users set user_inet = '${MachineIP}', user_port=${Uport} where user_inet isnull; \n\
  update mychips.users_v set peer_inet = '${MachineIP}', peer_port=${Pport0}, host_id='${Host0}' where peer_ent = 10000; \n\
  update mychips.users_v set peer_inet = '${MachineIP}', peer_port=${Pport1}, host_id='${Host1}' where peer_ent = 10001; \n\
  select count(*) as count from mychips.users_v where id >= 10000; \n\
  commit;`

//Initiate a tally for user 10001
const sqlTallyStart = "begin; \n\
  delete from mychips.tallies; \n\
  insert into mychips.tallies (tally_ent, tally_guid, partner, user_sig) values (10001, '18d44de5-837d-448f-8d96-9136372987cf',10000,'Adam signature'); \n\
  update mychips.tallies set request = 'draft' where tally_ent = 10001 and status = 'void' returning status;	-- Only update (not insert) triggers will generate requests \n\
  commit;"

describe("Peer to peer tallies", function() {
  var server1, server2
  var db, dbc

  before('Connect to (or create) test database', function(done) {
    var conf = {database: DatabaseName, listen: 'ForceOpen', logger:log}
    db = new dbClient(conf, (chan, data) => {
      log.info("Notify from channel:", chan, "data:", data)
    }, ()=>{log.debug("Connected"); done()})
  })

  before('Launch two peer servers', function() {
    server0 = new PeerCont(Pport0, Host0, {database: DatabaseName})
    server1 = new PeerCont(Pport1, Host1, {database: DatabaseName})
  })

  it("Check for correct number of test users", function(done) {
    db.query(sqlUserInit, null, (err, res) => { if (err) done(err)
      var count = res[4].rows[0]['count']
//console.log("Users:", count)
      assert.equal(count,2)
      done()
    })
  })

  it("User 10001 proposes a tally to user 10000", function(done) {
    db.query(sqlTallyStart, null, (err, res) => { if (err) done(err)
      var stat = res[3].rows[0]['status']
      log.debug("SQL Done:", stat)
      assert.equal(stat, 'void')
    })

    var conf = {database: DatabaseName, listen: 'mychips_user_10000'}
    dbc = new dbClient(conf, (chan, data) => {
      log.info("Notify from channel:", chan, "data:", data)
      var msg = JSON.parse(data)
      log.trace("foil:", msg.foil)
      assert.equal(msg.foil, 'james_madison.chip')
      log.trace("signed.foil:", msg.signed.foil)
//      assert.equal(msg.signed.foil, null)
      done()
    }, ()=>{log.debug("Temp client connected")})
  })

  after('Disconnect from test database', function(done) {
    dbc.disconnect()
    db.disconnect()
    server0.close()
    server1.close()
    done()
  })
});

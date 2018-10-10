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
const MessageBus = require('../bus')
const MachineIP = "192.168.57.101"
const Uport=43210
const Pport0=65430
const Pport1=65431
const Host0 = "server0"
const Host1 = "server1"
var log = require('../../lib/logger')('testpeer')
var { dbClient } = require("wyseman")

//Initialize test users
const sqlUserInit = `begin; \n\
  update mychips.users set user_inet = '${MachineIP}', user_port=${Uport} where user_inet isnull; \n\
  update mychips.users_v set peer_inet = '${MachineIP}', peer_port=${Pport0}, host_id='${Host0}' where peer_ent = 10000; \n\
  update mychips.users_v set peer_inet = '${MachineIP}', peer_port=${Pport1}, host_id='${Host1}' where peer_ent = 10001; \n\
  select count(*) as count from mychips.users_v where id >= 10000; \n\
  commit;`

//Initiate a tally for user 10001
const sqlTallyStart = "begin; \n\
  delete from mychips.tallies; \n\
  insert into mychips.tallies (tally_ent, tally_guid, partner, user_sig, contract) values (10001, '18d44de5-837d-448f-8d96-9136372987cf',10000,'Adam signature', 'mychips-0.99'); \n\
  update mychips.tallies set request = 'draft' where tally_ent = 10001 and status = 'void' returning status;	-- Only update (not insert) triggers will generate requests \n\
  commit;"

const sqlTallyState = "select state from mychips.tallies_v where tally_ent = $1 and tally_seq = $2"	//Fetch tally state
const sqlTallyCounter = "update mychips.tallies set contract = $1, status='void', request = 'draft', user_sig = $2, part_sig = null where tally_ent = $3 and status = 'draft' returning status;"
const sqlTallyAccept = "update mychips.tallies set request = 'open', user_sig = $1 where tally_ent = $2 and status = 'draft' returning status;"

describe("Peer to peer tallies", function() {
  var server1, server2
  var bus0 = new MessageBus('bus0'), bus1 = new MessageBus('bus1')
  var db0, db1

  before('Connection 0 to test database', function(done) {
    db0 = new dbClient({database: DatabaseName, listen: 'mychips_user_10000', logger:log}, (chan, data) => {
      log.info("Notify from channel:", chan, "data:", data)
      bus0.notify(data)
    }, ()=>{log.debug("Main test DB connection 0 established"); done()})
  })

  before('Connection 1 to test database', function(done) {
    db1 = new dbClient({database: DatabaseName, listen: 'mychips_user_10001', logger:log}, (chan, data) => {
      log.info("Notify from channel:", chan, "data:", data)
      bus1.notify(data)
    }, ()=>{log.debug("Main test DB connection 1 established"); done()})
  })

  before('Launch two peer servers', function() {
    server0 = new PeerCont(Pport0, Host0, {database: DatabaseName})
    server1 = new PeerCont(Pport1, Host1, {database: DatabaseName})
  })

  it("Check for correct number of test users", function(done) {
    db0.query(sqlUserInit, null, (err, res) => { if (err) done(err)
      var count = res[4].rows[0]['count']
//console.log("Users:", count)
      assert.equal(count,2)
      done()
    })
  })

  it("User 10001 proposes a tally to user 10000", function(done) {
    db1.query(sqlTallyStart, null, (err, res) => { if (err) done(err)
      var stat = res[3].rows[0]['status']
      log.debug("SQL Done:", stat)
      assert.equal(stat, 'void')
    })

    bus0.register('p0', (data) => {var msg = JSON.parse(data)
      log.debug("Check foil:", msg.foil)
      assert.equal(msg.foil, 'james_madison.chip')
      log.debug("signed.foil:", msg.signed.foil)
      assert.equal(msg.signed.foil, null)
      bus0.register('p0')
      done()
    })
  })

  it("User 10000 verfies the tally", function(done) {
    db0.query(sqlTallyState, [10000,1], (err, res) => { if (err) done(err)
      var state = res.rows[0]['state']
      log.debug("Tally State:", state)
      assert.equal(state, 'peerProffer')
      done()
    })
  })

  it("User 10000 counters the tally", function(done) {
    db0.query(sqlTallyCounter, ['mychips-1.0','James Signature','10000'], (err, res) => { if (err) done(err)
      log.debug("Counter:", res.rows)
      var status = res.rows[0]['status']
      log.debug("Counter Status:", status)
      assert.equal(status, 'void')
    })

    bus1.register('p1', (data) => {var msg = JSON.parse(data)
      log.trace("Check contract:", msg.contract)
      assert.equal(msg.contract, 'mychips-1.0')
      log.debug("status:", msg.status)
//      assert.equal(msg.signed.foil, null)
      bus1.register('p1')
      done()
    })
  })

  it("User 10001 accepts the tally", function(done) {
    db1.query(sqlTallyAccept, ['Adam Signature','10001'], (err, res) => { if (err) done(err)
      log.trace("Accept:", res.rows)
      var status = res.rows[0]['status']
      log.debug("Accept Status:", status)
      assert.equal(status, 'draft')
    })

    bus0.register('a0', (data) => {var msg = JSON.parse(data)
      log.debug("Accept contract:", msg.signed)
      assert.equal(msg.signed.stock, 'Adam Signature')
      bus1.register('a0')
      done()
    })
  })

  after('Disconnect from test database', function(done) {
    db0.disconnect()
    db1.disconnect()
    server0.close()
    server1.close()
    done()
  })
});

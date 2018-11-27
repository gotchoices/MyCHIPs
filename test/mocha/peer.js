//Test tallys and chits between peers
//TODO:
//- Sometimes this test doesn't terminate.  Why?
//- 
//- Create test for each pathway of the flow chart
//- Check the state of the database after each stage
//- Create similar testing for chit flowchart
//- 

const assert = require("assert");
const PeerCont = require("../../lib/peer")
const { DatabaseName, MachineIP } = require('../settings')
const MessageBus = require('../bus')
const Uport=43210
const Pport0=65430
const Pport1=65431
const Host0 = "server0"
const Host1 = "server1"
var log = require('../../lib/logger')('testpeer')
var { dbClient } = require("wyseman")

describe("Peer to peer tallies", function() {
  var server1, server2
  var bus0 = new MessageBus('bus0'), bus1 = new MessageBus('bus1')
  var db0, db1

  before('Connection 0 to test database', function(done) {
    db0 = new dbClient({database: DatabaseName, listen: 'mychips_user_10000', logger:log}, (chan, data) => {
      log.info("Notify from channel:", chan, "data:", data)
      bus0.notify(data)
    }, ()=>{log.info("Main test DB connection 0 established"); done()})
  })

  before('Connection 1 to test database', function(done) {
    db1 = new dbClient({database: DatabaseName, listen: 'mychips_user_10001', logger:log}, (chan, data) => {
      log.info("Notify from channel:", chan, "data:", data)
      bus1.notify(data)
    }, ()=>{log.info("Main test DB connection 1 established"); done()})
  })

  before('Launch two peer servers', function() {
    server0 = new PeerCont(Pport0, Host0, {database: DatabaseName})
    server1 = new PeerCont(Pport1, Host1, {database: DatabaseName})
  })

  it("Check for correct number of test users", function(done) {
    const sql = `begin; \
      update mychips.users set user_inet = '${MachineIP}', user_port=${Uport} where user_inet isnull; \
      update mychips.users_v set peer_inet = '${MachineIP}', peer_port=${Pport0}, host_id='${Host0}' where peer_ent = 10000; \
      update mychips.users_v set peer_inet = '${MachineIP}', peer_port=${Pport1}, host_id='${Host1}' where peer_ent = 10001; \
      select count(*) as count from mychips.users_v where id >= 10000; commit;`
    db0.query(sql, null, (err, res) => { if (err) done(err)
      var count = res[4].rows[0]['count']
      log.info("Users:", count)
      assert.equal(count,2)
      done()
    })
  })

//    update mychips.tallies set request = 'draft' where tally_ent = 10001 and status = 'void' returning status;		-- Only update (not insert) triggers will generate requests
  it("User 10001 proposes a tally to user 10000", function(done) {
    const sql = `begin;
      delete from mychips.tallies;
      insert into mychips.tallies (tally_ent, tally_guid, partner, user_sig, contract, request) values (10001, '18d44de5-837d-448f-8d96-9136372987cf',10000,'Adam signature', 'mychips-0.99', 'draft') returning status;
      commit;`
    db1.query(sql, null, (err, res) => { if (err) done(err)
console.log("RES:", res[2].rows)
      var stat = res[2].rows[0]['status']
      log.info("1001 proposal done status:", stat)
      assert.equal(stat, 'void')
    })

    bus0.register('p0', (data) => {var msg = JSON.parse(data)
      log.info("Check foil:", msg.foil)
      assert.equal(msg.foil, 'james_madison.chip')
      log.info("signed.foil:", msg.signed.foil)
      assert.equal(msg.signed.foil, null)
      bus0.register('p0')
      done()
    })
  })

  it("User 10000 verfies the tally", function(done) {
    const sql = "select state from mychips.tallies_v where tally_ent = $1 and tally_seq = $2;"	//Fetch tally state
    db0.query(sql, [10000,1], (err, res) => { if (err) done(err)
      var state = res.rows[0]['state']
      log.info("Tally State:", state)
      assert.equal(state, 'peerProffer')
      done()
    })
  })

  it("User 10000 counters the tally", function(done) {
    const sql = "update mychips.tallies set contract = $1, status='void', request = 'draft', user_sig = $2, part_sig = null where tally_ent = $3 and status = 'draft' returning status;"
    db0.query(sql, ['mychips-1.0','James Signature','10000'], (err, res) => { if (err) done(err)
      log.info("Counter:", res.rows)
      var status = res.rows[0]['status']
      log.info("Counter Status:", status)
      assert.equal(status, 'void')
    })

    bus1.register('p1', (data) => {var msg = JSON.parse(data)
      log.trace("Check contract:", msg.contract)
      assert.equal(msg.contract, 'mychips-1.0')
      log.info("status:", msg.status)
//      assert.equal(msg.signed.foil, null)
      bus1.register('p1')
      done()
    })
  })

  it("User 10001 accepts the tally", function(done) {
    const sql = "update mychips.tallies set request = 'open', user_sig = $1 where tally_ent = $2 and status = 'draft' returning status;"
    db1.query(sql, ['Adam Signature','10001'], (err, res) => { if (err) done(err)
      log.trace("Accept:", res.rows)
      var status = res.rows[0]['status']
      log.info("Accept Status:", status)
      assert.equal(status, 'draft')
    })

    bus0.register('a0', (data) => {var msg = JSON.parse(data)
      log.info("Accept contract:", msg.signed)
      assert.equal(msg.signed.stock, 'Adam Signature')
      bus0.register('a0')
      done()
    })
  })

  it("User 10001 requests payment from user 10000", function(done) {
    const sql = `begin;
      delete from mychips.chits;
      insert into mychips.chits (chit_ent, chit_seq, chit_guid, chit_type, units, pro_quo, request) values (10001, 1, 'd0921c68-de42-4087-9af1-0664605d4136', 'tran', 12345600, 'Consulting', 'userRequest') returning units;
      commit;`
    db1.query(sql, null, (err, res) => { if (err) done(err)
      var units = res[2].rows[0]['units']
      log.info("10001 invoice done units:", units)
      assert.equal(units, '12345600')
    })

    bus0.register('c0', (data) => {var msg = JSON.parse(data)
      log.info("Check chit:", msg)
      assert.equal(msg.units, 12345600)
      log.info("Signature:", msg.signature)
      assert.equal(msg.signature, null)
      bus0.register('c0')
      done()
    })
  })

  it("User 10000 agrees to pay user 10001's invoice", function(done) {
    const sig = "James Signature"
    const sql = `update mychips.chits set request = 'userAgree', signature='${sig}' where chit_ent = 10000 and signature is null returning signature;`
    db1.query(sql, null, (err, res) => { if (err) done(err)
      var signature = res.rows[0]['signature']
      log.info("10001 invoice paid by 10000:", signature)
      assert.equal(signature, sig)
    })

    bus1.register('c1', (data) => {var msg = JSON.parse(data)
      log.info("Payment request approved:", msg)
      assert.equal(msg.units, 12345600)
      log.info("Signature:", msg.signed)
      assert.equal(msg.signed, sig)
      bus1.register('c1')
      done()
    })
  })

  it("User 10001 sends partial refund to user 10000", function(done) {
    const sql = "begin; \n\
      insert into mychips.chits (chit_ent, chit_seq, chit_guid, chit_type, units, pro_quo) values (10001, 1, '1a7e3036-7f3e-40f7-b386-0af972ee77f5', 'tran', -2345600, 'Partial refund'); \n\
      update mychips.chits set request = 'userDraft', signature='Adam Signature' where chit_ent = 10001 and signature is null returning units; commit;"
    db1.query(sql, null, (err, res) => { if (err) done(err)
      var units = res[2].rows[0]['units']
      log.info("10001 refund done units:", units)
      assert.equal(units, -2345600)
    })

    bus0.register('c0', (data) => {var msg = JSON.parse(data)
      log.info("Check refund chit:", msg)
      assert.equal(msg.units, -2345600)
      bus0.register('c0')
      done()
    })
  })

  after('Disconnect from test database', function(done) {
    setTimeout(()=>{		//Let everything flush out before closing
      db0.disconnect()
      db1.disconnect()
      server0.close()
      server1.close()
      }, 500)
    done()
  })
});

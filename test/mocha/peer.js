//Test tallys and chits between peers
//TODO:
//- Sometimes this test doesn't terminate.  Why?
//- 
//- Create test for each pathway of the flow chart
//- Check the state of the database after each stage
//- Create similar testing for chit flowchart
//- 

const assert = require('assert');
const { DatabaseName, DBAdmin, MachineIP, Log } = require('../settings')
var log = Log('test-peer', 'info', 'mychips-test')
const PeerCont = require("../../lib/peer")
const MessageBus = require('../bus')
const Uport=43210
const Pport0=65434
const Pport1=65435
const Host0 = "server0"
const Host1 = "server1"
var { dbClient } = require("wyseman")
var interTest = {}			//Pass values from one test to another

describe("Peer to peer tallies", function() {
  var server1, server2
  var bus0 = new MessageBus('bus0'), bus1 = new MessageBus('bus1')
  var db0, db1

  before('Connection 0 to test database', function(done) {	//Emulate user p1000
    db0 = new dbClient({database: DatabaseName, user: DBAdmin, listen: 'mychips_user_p1000', log}, (chan, data) => {
      log.info("Notify 0 from channel:", chan, "data:", data)
      bus0.notify(data)
    }, ()=>{log.info("Main test DB connection 0 established"); done()})
  })

  before('Connection 1 to test database', function(done) {	//Emulate user p1001
    db1 = new dbClient({database: DatabaseName, user: DBAdmin, listen: 'mychips_user_p1001', log}, (chan, data) => {
      log.info("Notify 1 from channel:", chan, "data:", data)
      bus1.notify(data)
    }, ()=>{log.info("Main test DB connection 1 established"); done()})
  })

  before('Launch two peer servers', function() {
    server0 = new PeerCont({port:Pport0, servID:Host0}, {database: DatabaseName, user: DBAdmin, log})
    server1 = new PeerCont({port:Pport1, servID:Host1}, {database: DatabaseName, user: DBAdmin, log})
  })

  it("Check for correct number of test users", function(done) {
    const sql = `begin; \
      update mychips.users set user_host = '${MachineIP}', user_port=${Uport} where user_host isnull; \
      update mychips.users_v set peer_host = '${MachineIP}', peer_port=${Pport0}, serv_id='${Host0}' where peer_ent = 'p1000'; \
      update mychips.users_v set peer_host = '${MachineIP}', peer_port=${Pport1}, serv_id='${Host1}' where peer_ent = 'p1001'; \
      select count(*) as count from mychips.users_v where ent_num >= 1000; commit;`
    db0.query(sql, null, (err, res) => {if (err) done(err)
      assert.equal(res.length, 6)
      let row = res[4].rows[0]
      log.info("Users:", row.count)
      assert.equal(row.count,2)
      done()
    })
  })

  it("User p1001 proposes a tally to user p1000", function(done) {
    const sql = `begin;
      delete from mychips.tallies;
      insert into mychips.tallies (tally_ent, tally_guid, partner, user_sig, contract, request) 
        values ('p1001', '18d44de5-837d-448f-8d96-9136372987cf','p1000','Adam signature', '{\"name\":\"mychips-0.99\"}'::jsonb, 'draft') returning status, tally_seq;
      commit;`
    db1.query(sql, null, (err, res) => { if (err) done(err)
//console.log("RES:", res[2], "err:", err ? err.detail : null)
      assert.equal(res.length, 4)
      assert.equal(res[2].rows.length, 1)
      let row = res[2].rows[0]
      interTest.seq = row.tally_seq
      log.info("1001 proposal done; status:", row.status, "seq:", row.tally_seq)
      assert.equal(row.status, 'void')
    })

    bus0.register('p0', (data) => {
      let msg = JSON.parse(data)
        , obj = msg.object
      log.info("Check foil:", obj.foil, obj)
      assert.equal(obj.foil, 'james_madison')
      log.info("  signed.foil:", obj.signed.foil)
      assert.equal(obj.signed.foil, null)
      bus0.register('p0')
      done()
    })
  })

  it("User p1000 verifies the tally", function(done) {
    const sql = "select state from mychips.tallies_v where tally_ent = $1 order by tally_seq desc limit 1;"	//Fetch tally state
    db0.query(sql, ['p1000'], (err, res) => { if (err) done(err)
      assert.equal(res.rows.length, 1)
      let row = res.rows[0]
      log.info("Tally State:", row.state)
      assert.equal(row.state, 'peerProffer')
      done()
    })
  })

  it("User p1000 counters the tally", function(done) {
    const sql = "update mychips.tallies set contract = $1, status='void', request = 'draft', user_sig = $2, part_sig = null where tally_ent = $3 and status = 'draft' returning status;"
    db0.query(sql, [{name:'mychips-1.0'},'James Signature','p1000'], (err, res) => { if (err) done(err)
      assert.equal(res.rows.length, 1)
      log.info("Counter rows:", res.rows.length)
      let row = res.rows[0]
      log.info("Counter Status:", row.status)
      assert.equal(row.status, 'void')
    })

    bus1.register('p1', (data) => {
      let msg = JSON.parse(data)
        , obj = msg.object
      log.info("Check contract:", obj)
//console.log("Contract:", obj.contract, typeof obj.contract)
      assert.equal(obj.contract.name, 'mychips-1.0')
      log.info("  contract:", obj.contract)
      bus1.register('p1')
      done()
    })
  })

  it("User p1001 accepts the tally", function(done) {
    const sql = "update mychips.tallies set request = 'open', user_sig = $1 where tally_ent = $2 and status = 'draft' returning status;"
    db1.query(sql, ['Adam Signature','p1001'], (err, res) => { if (err) done(err)
      assert.equal(res.rows.length, 1)
      log.debug("Accept:", res.rows.length)
      let row = res.rows[0]
      log.info("Accept Status:", row.status, "seq:", row.tally_seq)
      assert.equal(row.status, 'draft')
    })

    bus0.register('a0', (data) => {
      let msg = JSON.parse(data)
        , obj = msg.object
      log.info("Accept contract:", obj.signed)
      assert.equal(obj.signed.stock, 'Adam Signature')
      bus0.register('a0')
      done()
    })
  })

  it("User p1001 requests payment from user p1000", function(done) {
    const sql = `begin;
      delete from mychips.chits;
      insert into mychips.chits (chit_ent, chit_seq, chit_guid, chit_type, units, quidpro, request) 
        values ('p1001', ${interTest.seq}, 'd0921c68-de42-4087-9af1-0664605d4136', 'tran', 12345600, 'Consulting', 'userRequest') returning units;
      commit;`
log.debug("Sql:", sql)
    db1.query(sql, null, (err, res) => { if (err) done(err)
      assert.equal(res.length, 4)
      assert.equal(res[2].rows.length, 1)
      log.debug("p1001 invoice res:", res[2].rows.length)
      let row = res[2].rows[0]
      assert.equal(row.units, '12345600')
      log.info("p1001 invoice done units:", row.units)
    })

    bus0.register('c0', (data) => {
      let msg = JSON.parse(data)
      log.info("Check chit:", msg)
      assert.equal(msg.units, 12345600)
      log.info("Signature:", msg.signature)
      assert.equal(msg.signature, null)
      bus0.register('c0')
      done()
    })
  })

  it("User p1000 agrees to pay user p1001's invoice", function(done) {
    const sig = "James Signature"
    const sql = `update mychips.chits set request = 'userAgree', signature='${sig}' where chit_ent = 'p1000' and signature is null returning signature;`
    db1.query(sql, null, (err, res) => { if (err) done(err)
      assert.equal(res.rows.length, 1)		//Should find one row
      let row = res.rows[0]
      log.info("p1001 invoice paid by p1000:", row.signature)
      assert.equal(row.signature, sig)
    })

    bus1.register('c1', (data) => {
      let msg = JSON.parse(data)
      log.info("Payment request approved:", msg)
      assert.equal(msg.units, 12345600)
      log.info("Signature:", msg.signed)
      assert.equal(msg.signed, sig)
      bus1.register('c1')
      done()
    })
  })

  it("User p1001 sends partial refund to user p1000", function(done) {
    let guid = '1a7e3036-7f3e-40f7-b386-0af972ee77f5'
      , sql = `begin;
      insert into mychips.chits (chit_ent, chit_seq, chit_guid, chit_type, units, quidpro) 
        values ('p1001', ${interTest.seq}, '${guid}', 'tran', -2345600, 'Partial refund');
      update mychips.chits set request = 'userDraft', signature='Adam Signature' where chit_ent = 'p1001' and chit_guid = '${guid}' and signature is null returning units; 
      commit;`
    db1.query(sql, null, (err, res) => { if (err) done(err)
      let units = res[2].rows[0]['units']
      log.info("p1001 refund done units:", units)
      assert.equal(units, -2345600)
    })

    bus0.register('c0', (data) => {
      let msg = JSON.parse(data)
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
});		//Peer to peer talies

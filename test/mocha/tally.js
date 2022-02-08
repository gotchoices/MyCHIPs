//Test tally initialization sequence; Run only after impexp, testusers
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// This simulates two users connected through a single DB:
// User1 <-> DB <-> Agent1 <-> Agent2 <-> DB <-> User2
//TODO:
//X- Give ticket info to other peer
//X- Have them connect via noise module using the ticket
//- Test for one-time connection, token no longer valid
//- Test for reusable token, tally is cloned, token still valid
//- 

const { dbConf, Log, Format, Bus, assert, saveRest, getRow, mkUuid } = require('../settings')
var log = Log('testTally')
var { dbClient } = require("wyseman")
const PeerCont = require("../../lib/peer2peer")
const {host,user0,user1,cid0,cid1,Port0,Port1,agent0,agent1,aCon0,aCon1} = require('./testusers')
var contract = {domain:"mychips.org", name:"deluxe", version:1.0}
var interTest = {}			//Pass values from one test to another

describe("Establish new tally between two users", function() {
  var server0, server1
  var bus0 = new Bus('bus0'), bus1 = new Bus('bus1')
  var db0, db1

  before('Connection 0 to test database', function(done) {	//Emulate user p1000
    db0 = new dbClient(new dbConf(log,'mychips_user_p1000'), (chan, data) => {
      log.trace("Notify 0 from channel:", chan, "data:", data)
      bus0.notify(data)
    }, ()=>{log.info("Main test DB connection 0 established"); done()})
  })

  before('Connection 1 to test database', function(done) {	//Emulate user p1001
    db1 = new dbClient(new dbConf(log,'mychips_user_p1001'), (chan, data) => {
      log.trace("Notify 1 from channel:", chan, "data:", data)
      bus1.notify(data)
    }, ()=>{log.info("Main test DB connection 1 established"); done()})
  })

  before('Launch two peer servers', function(done) {
    server0 = new PeerCont(aCon0, new dbConf())		//Smith
    server1 = new PeerCont(aCon1, new dbConf())		//Madison
    done()
  })

  it("Initialize DB", function(done) {
    let sql = `begin;
        delete from mychips.tallies;
        update mychips.users set _last_tally = 0; commit`
    db0.query(sql, (e) => {if (e) done(e); done()})
  })

  it("User 0 proposer builds tally template and token", function(done) {
    let cid = user0
      , uuid = mkUuid(cid)
      , s1 = Format('insert into mychips.tallies (tally_ent, tally_uuid, contract) values(%L,%L,%L)', cid, uuid, contract)
      , sql = `with row as (${s1} returning tally_ent, tally_seq)
          insert into mychips.tokens (token_ent, tally_seq) select * from row returning *;
          select * from mychips.tallies_v where tally_ent = '${cid}' and tally_seq = 1;
          select token,expires,chad from mychips.tokens_v;`
//log.debug("Sql:", sql)
    db0.query(sql, (e, res) => {if (e) done(e)
//log.debug("Res:", res)
      assert.equal(res.length, 3)
      assert.equal(res[0].rowCount, 1)
      let tok = res[0].rows[0]
      assert.equal(tok.token_ent, cid)
      assert.equal(tok.token_seq, 1)
      assert.equal(tok.tally_seq, 1)
      assert.equal(tok.token.length, 32)	//MD5
      let tal = res[1].rows[0]
//log.debug("Talley:", tal)
      assert.equal(tal.tally_uuid, uuid)
      assert.ok(!tal.partner)
      assert.equal(tal.status,'draft')
      assert.equal(tal.tally_type,'stock')
      assert.equal(tal.hold_cid,cid0)
      assert.equal(tal.hold_agent,agent0)
      let ticket = res[2].rows[0]
//log.debug("Ticket:", ticket)
      interTest = ticket
      done()
    })
  })

  it("User 1 subject asks his server to request the proposed tally", function(done) {
    let sql = Format('select mychips.ticket_process(%L,%L)', interTest, user1)
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
//log.debug("Sql:", sql)
    db1.query(sql, null, (e, res) => { if (e) done(e)
      let row = getRow(res, 0)
//log.debug("row:", row);
      assert.ok(row.ticket_process)
      _done()
    })
    bus0.register('p0', (data) => {		//User 0 is prompted to sign the tally
      let msg = JSON.parse(data)
//log.debug("msg:", msg)
      assert.equal(msg.entity, 'p1000')
      assert.equal(msg.state, 'draft')
      let tally = msg.object
        , stock = tally.stock
        , foil = tally.foil
//log.debug("tally:", tally, tally.stock.cert.chad)
      assert.equal(stock.cert.chad.cid, cid0)
      assert.equal(stock.cert.chad.agent, agent0)
      assert.equal(foil.cert.chad.cid, cid1)
      assert.equal(foil.cert.chad.agent, agent1)
//log.debug("sign:", tally.sign)
      assert.ok(!tally.sign.stock)
      assert.ok(!tally.sign.foil)
      bus0.register('p0')
      _done()
    })
  })

  it("User 0 originator approves, signs the proposed tally", function(done) {
    let sql = "update mychips.tallies set request = $1, hold_sig = $2 where tally_ent = $3 and tally_seq = $4 returning request, status;"
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
//log.debug("Sql:", sql)
    db0.query(sql, ['offer','Adam Signature',user0,1], (err, res) => { if (err) done(err)
      let row = getRow(res, 0)			//;log.debug("row:", row);
      assert.equal(row.request, 'offer')
      assert.equal(row.status, 'draft')
      _done()
    })
    bus1.register('p1', (data) => {		//User 0 is sent the signed tally
      let msg = JSON.parse(data)		//;log.debug("msg:", msg)
      assert.equal(msg.entity, 'p1001')
      assert.equal(msg.state, 'peerProffer')
      let tally = msg.object
        , stock = tally.stock
        , foil = tally.foil
//log.debug("tally:", tally, tally.stock.cert.chad)
      assert.equal(stock.cert.chad.cid, cid0)
      assert.equal(stock.cert.chad.agent, agent0)
      assert.equal(foil.cert.chad.cid, cid1)
      assert.equal(foil.cert.chad.agent, agent1)
//log.debug("sign:", tally.sign)
      assert.ok(!!tally.sign.stock)
      assert.ok(!tally.sign.foil)
      interTest = tally
      bus1.register('p1')
      _done()
    })
  })

  it("User 0 originator's tally got promoted, correct state", function(done) {
    let sql = "select * from mychips.tallies_v where tally_ent = $1 and tally_uuid = $2;"
      , uuid = interTest.uuid
//log.debug("Sql:", sql)
    db0.query(sql, [user0, uuid], (err, res) => { if (err) done(err)
      let row = getRow(res, 0)			//;log.debug("row:", row);
      assert.equal(row.tally_type, 'stock')
      assert.equal(row.state, 'userProffer')
      assert.equal(row.status, 'offer')
      assert.ok(!!row.hold_sig)
      assert.ok(!row.part_sig)
      done()
    })
  })

/*
xxxx
  it("User p1001 proposes a tally to user p1000", function(done) {
    const sql = `begin;
      delete from mychips.tallies;
      insert into mychips.tallies (tally_ent, tally_uuid, partner, hold_sig, contract, request) 
        values ('p1001', '18d44de5-837d-448f-8d96-9136372987cf','p1000','Adam signature', '{\"name\":\"mychips-0.99\"}'::jsonb, 'draft') returning status, tally_seq;
      commit;`
//log.debug("Sql:", sql)
    db1.query(sql, null, (err, res) => { if (err) done(err)
//log.debug("RES:", res[2], "err:", err ? err.detail : null)
      assert.equal(res.length, 4)		//begin, delete, insert, commit
      assert.equal(res[2].rows.length, 1)
      let row = res[2].rows[0]
      interTest.seq = row.tally_seq		//remember sequence for later
      log.info("1001 proposal done; status:", row.status, "seq:", row.tally_seq)
      assert.equal(row.status, 'void')
    })

    bus0.register('p0', (data) => {		//Listen for message from our database
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
    const sql = "update mychips.tallies set contract = $1, status='void', request = 'draft', hold_sig = $2, part_sig = null where tally_ent = $3 and status = 'draft' returning status;"
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
    const sql = "update mychips.tallies set request = 'open', hold_sig = $1 where tally_ent = $2 and status = 'draft' returning status;"
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
      insert into mychips.chits (chit_ent, chit_seq, chit_uuid, chit_type, units, quidpro, request) 
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
    let uuid = '1a7e3036-7f3e-40f7-b386-0af972ee77f5'
      , sql = `begin;
      insert into mychips.chits (chit_ent, chit_seq, chit_uuid, chit_type, units, quidpro) 
        values ('p1001', ${interTest.seq}, '${uuid}', 'tran', -2345600, 'Partial refund');
      update mychips.chits set request = 'userDraft', signature='Adam Signature' where chit_ent = 'p1001' and chit_uuid = '${uuid}' and signature is null returning units; 
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
*/
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{		//Let everything flush out before closing
      db0.disconnect()
      db1.disconnect()
      server0.close()
      server1.close()
      }, 500)
    done()
  })
});		//Peer to peer tallies

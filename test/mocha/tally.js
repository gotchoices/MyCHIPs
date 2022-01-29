//Test tally initialization sequence; Run only after impexp done
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// This simulates two users connected through a single DB:
// User1 <-> DB <-> Agent1 <-> Agent2 <-> DB <-> User2
//TODO:
//X- Create tally template
//X- Attach token to it
//- Give ticket info to other peer
//- Have them connect via noise module using the ticket
//- 
//- Test for one-time connection, token no longer valid
//- Test for reusable token, tally is cloned, token still valid
//- 

const assert = require('assert');
const uuidv5 = require('uuid/v5')
const Format = require('pg-format')
const { Database, DBAdmin, MachineIP, Log } = require('../settings')
var log = Log('testPeer')
var { dbClient } = require("wyseman")
const PeerCont = require("../../lib/peer")
const MessageBus = require('../bus')
const Port0=65434
const Port1=65435
var host = 'localhost'
var publicKey0 = Buffer.from('P'+Port0).toString('base64url')
var publicKey1 = Buffer.from('Q'+Port1).toString('base64url')
var agent0 = {host, port: Port0, key:{publicKey:publicKey0}}
var agent1 = {host, port: Port1, key:{publicKey:publicKey1}}
var interTest = {}			//Pass values from one test to another
var dbConf = function(listen) {Object.assign(this, {database: Database, user: DBAdmin, log, listen})}

describe("Establish new tally", function() {
  var server0, server1
  var bus0 = new MessageBus('bus0'), bus1 = new MessageBus('bus1')
  var db0, db1

  before('Connection 0 to test database', function(done) {	//Emulate user p1000
    db0 = new dbClient(new dbConf('mychips_user_p1000'), (chan, data) => {
      log.info("Notify 0 from channel:", chan, "data:", data)
      bus0.notify(data)
    }, ()=>{log.info("Main test DB connection 0 established"); done()})
  })

  before('Connection 1 to test database', function(done) {	//Emulate user p1001
    db1 = new dbClient(new dbConf('mychips_user_p1001'), (chan, data) => {
      log.info("Notify 1 from channel:", chan, "data:", data)
      bus1.notify(data)
    }, ()=>{log.info("Main test DB connection 1 established"); done()})
  })

  before('Launch two peer servers', function(done) {
    server0 = new PeerCont(agent0, new dbConf())	//Smith
    server1 = new PeerCont(agent1, new dbConf())	//Madison
    done()
  })

  it("Initialize test users", function(done) {
//log.debug("Key:", agent0.key.publicKey)
    let fields = 'peer_host = %L, peer_port=%L, peer_agent=%L'
      , f0 = Format(fields, host, Port0, publicKey0)
      , f1 = Format(fields, host, Port1, publicKey1)
      , sql = `begin;
        delete from base.ent where ent_num > 1001;
        delete from mychips.tallies;
        update mychips.users set _last_tally = 0;
        update mychips.users_v set ${f0} where peer_ent = 'p1000';
        update mychips.users_v set ${f1} where peer_ent = 'p1001';
        select count(*) as count from mychips.users_v where ent_num >= 1000; commit;`
log.debug("Sql:", sql)
    db0.query(sql, (err, res) => {if (err) done(err)
      assert.equal(res.length, 8)	//8: begin, del, del, upd, upd, upd, select, commit
//log.debug("Res:", res[6].rows[0])
      let row = res[6].rows[0]
log.info("Users:", row.count)
      assert.equal(row.count,2)
      done()
    })
  })

  it("p1000 builds proposed tally and token", function(done) {
    let cid = 'p1000'
      , uuidNS = uuidv5(cid, uuidv5.DNS)
      , uuid = uuidv5(cid, uuidNS)
      , contract = {name:"mychips", version:0.99}
      , s1 = Format('insert into mychips.tallies (tally_ent, tally_uuid, contract) values(%L,%L,%L)', cid, uuid, contract)
      , sql = `with row as (${s1} returning tally_ent, tally_seq)
          insert into mychips.tokens (token_ent, tally_seq) select * from row returning *;
          select * from mychips.tallies where tally_ent = '${cid}' order by tally_seq desc limit 1;
          select chip,token,expires from mychips.tokens_v;`
//log.debug("Sql:", sql)
    db0.query(sql, (e, res) => {if (e) done(e)
//log.debug("Res:", res)
      assert.equal(res.length, 3)
      assert.equal(res[0].rowCount, 1)
      let tok = res[0].rows[0]
//log.debug("Tok:", tok)
      assert.equal(tok.token_ent, cid)
      assert.equal(tok.token_seq, 1)
      assert.equal(tok.tally_seq, 1)
      assert.equal(tok.token.length, 32)	//MD5
      let tal = res[1].rows[0]
//log.debug("Talley:", tal)
      assert.equal(tal.tally_uuid, uuid)
      assert.ok(!tal.partner)
      assert.equal(tal.status,'void')
//log.debug("Ticket:", res[2].rows[0])
      interTest = res[2].rows[0]
      done()
    })
  })

  it("p1001 asks his server to request the proposed tally", function(done) {
    let sql = Format('select mychips.ticket_process(%L,%L)', interTest, 'p1001')
log.debug("Sql:", sql)
    db1.query(sql, null, (e, res) => { if (e) done(e)
//log.debug("res:", res.rows[0]);
      assert.equal(res.rowCount, 1)
    })
    bus1.register('p1', ({chan, data}) => {	//Listen for message from our database
      let msg = JSON.parse(data)
log.debug("bus:", chan, msg)
      assert.equal(chan, listen1[0])		//Proper listen tag came through
      let cert = msg.cert
log.debug("cert:", cert)
      assert.equal(cert.id, 'p1000')
      bus1.register('p1')
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

//Test chits between peers; Run only after tally tests
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- Create sch-chit that tests only schema states
//- Remove old parts pertaining to tallies
//- Adjust to work with user agents
//- Adapt to Version 1 protocol
//- Test all modes/transitions on chit state diagram
//- 

const { dbConf, Log, Format, Bus, assert, getRow, mkUuid } = require('../settings')
var log = Log('testChit')
var { dbClient } = require("wyseman")
const PeerCont = require("../../lib/peer2peer")
var {save, rest} = require('./def-tally')
const {host,user0,user1,user2,cid0,cid1,cid2,agent0,agent1,agent2,aCon0,aCon1,aCon2,db2Conf} = require('./def-users')
var interTest = {}			//Pass values from one test to another

var Suite1 = function({sites, dbcO, dbcS, dbcSO, dbcSS, cidO, cidS, userO, userS, agentO, agentS, aConO, aConS, saveName}) {
  var serverO, serverS
  var busO = new Bus('busO'), busS = new Bus('busS')
  var dbO, dbS

  before('Connection 0 to test database', function(done) {	//Emulate originator user
    dbO = new dbClient(dbcO, (chan, data) => {
      log.trace("Notify 0 from channel:", chan, "data:", data)
      busO.notify(JSON.parse(data))
    }, ()=>{log.info("Main test DB connection 0 established"); done()})
  })

  before('Connection 1 to test database', function(done) {	//Emulate subject user
    dbS = new dbClient(dbcS, (chan, data) => {
      log.trace("Notify 1 from channel:", chan, "data:", data)
      busS.notify(JSON.parse(data))
    }, ()=>{log.info("Main test DB connection 1 established"); done()})
  })

  before('Launch two peer servers', function(done) {
    serverO = new PeerCont(aConO, dbcSO)
    serverS = new PeerCont(aConS, dbcSS)
    done()
  })

  it("Restore open tallies", function(done) {
    let dc = sites; _done = () => {if (!--dc) done()}
    dbO.query(rest(saveName), (e) => {if (e) done(e); else _done()})
    if (sites > 1) dbS.query(rest(saveName), (e) => {if (e) done(e); _done()})
  })

  it("Initialize DB", function(done) {
    let sql = `begin;
        delete from mychips.chits;
        update mychips.tallies set _last_chit = 0 where tally_ent = %L and status = 'open' returning tally_ent, tally_seq; commit`
      , dc = 2; _done = () => {if (!--dc) done()}	//dc _done's to be done
    dbO.query(Format(sql, userO), (e, res) => {if (e) done(e);
      assert.equal(res[2].rowCount, 1)
      let row = res[2].rows[0]			//;log.debug('row O:', row)
      assert.equal(row.tally_ent, userO)
      interTest.talO = row
      _done()
    })
    dbS.query(Format(sql, userS), (e, res) => {if (e) done(e);
      assert(res[2].rowCount, 1)
      let row = res[2].rows[0]			//;log.debug('row S:', row)
      assert.equal(row.tally_ent, userS)
      interTest.talS = row
      _done()
    })
  })

  it("Originator requests payment from Subject", function(done) {
    let uuid = mkUuid(cidO)
      , seq = interTest.talO.tally_seq
      , value = 1234500
      , reason = 'Consulting'
      , request = 'userRequest'
      , sql = Format(`insert into mychips.chits (chit_ent, chit_seq, chit_uuid, chit_type, units, quidpro, request)
          values (%L, %s, %L, 'tran', %s, %L, %L) returning *`, userO, seq, uuid, value, reason, request)
      , dc = 3; _done = () => {if (!--dc) done()}	//dc _done's to be done
log.debug("Sql:", sql)
    dbO.query(sql, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			;log.debug("row:", row);
      assert.equal(row.chit_ent, userO)
      assert.equal(row.chit_uuid, uuid)
      assert.equal(row.request, request)
      assert.equal(row.quidpro, reason)
      assert.ok(!row.chain_prv)
      assert.ok(!row.chain_idx)
      _done()
    })
    busS.register('ps', (msg) => {		//Subject is sent the payment request
log.debug("S user msg:", msg)
//      assert.equal(stock.cert.chad.cid, cidO)
      busS.register('ps')
      _done()
    })
    busO.register('po', (msg) => {		//Originator is sent the close request
log.debug("O user msg:", msg)
//      assert.equal(msg.entity, userO)
      busO.register('po')
      _done()
    })
  })

/* 
xxxx
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
      dbO.disconnect()
      dbS.disconnect()
      serverO.close()
      serverS.close()
      done()
      }, 200)
  })
}		//Suite 1

// Main
// ----------------------------------------------------------------------------
describe("Chit testing", function() {
  let config1 = {		//Two users on name host
    sites:1, saveName:'open1',
    cidO:cid0, cidS:cid1, userO:user0, userS:user1, aConO:aCon0, aConS:aCon1, agentO:agent0, agentS:agent1,
    dbcO: new dbConf(log, 'mychips_user_p1000'), 
    dbcS: new dbConf(log, 'mychips_user_p1001'),
    dbcSO: new dbConf(),
    dbcSS: new dbConf()
  }
  let config2 = {		//Two users on different hosts
    sites:2, saveName:'open2',
    cidO:cid0, cidS:cid2, userO:user0, userS:user2, aConO:aCon0, aConS:aCon2, agentO:agent0, agentS:agent2,
    dbcO: new dbConf(log, 'mychips_user_p1000'), 
    dbcS: db2Conf(log, 'mychips_user_p1002'),
    dbcSO: new dbConf(),
    dbcSS: db2Conf()
  }

  describe("Test chits between two users on same site", function() {Suite1(config1)})
//  describe("Test chits between two users on different sites", function() {Suite1(config2)})
})

//Test chits between peers; run 
//After: tally
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// This simulates two users connected through a single DB or two different DBs:
// User1 <-> DB <-> Agent1 <-> Agent2 <-> DB <-> User2
// User1 <-> DB1 <-> Agent1 <-> Agent2 <-> DB2 <-> User2
//TODO:
//- 
const { dbConf, testLog, Format, Bus, assert, getRow, mkUuid, dbClient, markLogs, SubCrypto, libModule, Stringify } = require('../common')
const log = testLog(__filename)
const crypto = new SubCrypto(log)
const PeerCont = require(libModule('peer2peer'))
const defTally = require('./def-tally')
const {uSql, save, rest, sSql} = require('./def-chit')
const {host,user0,user1,user2,cuid0,cuid1,cuid2,agent0,agent1,agent2,aCon0,aCon1,aCon2,db2Conf} = require('../def-users')
var interTest = {}			//Pass values from one test to another

var Suite1 = function({sites, dbcO, dbcS, dbcSO, dbcSS, cuidO, cuidS, userO, userS, agentO, agentS, aConO, aConS, saveName}) {
  var serverO, serverS
  var busO = new Bus('busO'), busS = new Bus('busS')
  var dbO, dbS

  const getSignature = function(db, user, uuid, done) {	//Make signature for existing chit
    let sql = sSql('c.json_core, u.user_cmt', user, uuid)	//;log.debug('sql:', sql)
    db.query(sql, (err, res) => { if (err) done(err)
      let row = getRow(res, 0)				//;log.debug("row:", row)
        , key = row.user_cmt				//;log.debug("key:", key)
        , message = Stringify(row.json_core)		//;log.debug('MS:', message)

      assert.ok(row.json_core)
      crypto.sign(key, message).then(sign => {
        let text = Buffer.from(sign).toString('base64url')
        assert.ok(text)			//;log.debug('sign:', text)
        interTest.sign = {key, sign, text, uuid}
        done()
      })
    })
  }

  before('Connection 0 to test database', function(done) {	//Emulate originator user
    dbO = new dbClient(dbcO, (chan, data, me) => {
      log.trace("Notify O from channel:", chan, me, "data:", data)
      busO.notify(JSON.parse(data))
    }, ()=>{log.info("Main test DB connection 0 established"); done()})
  })

  before('Connection 1 to test database', function(done) {	//Emulate subject user
    dbS = new dbClient(dbcS, (chan, data, me) => {
      log.trace("Notify S from channel:", chan, me, "data:", data)
      busS.notify(JSON.parse(data))
    }, ()=>{log.info("Main test DB connection 1 established"); done()})
  })

  before('Launch two peer servers', function(done) {
    serverO = new PeerCont(aConO, dbcSO)
    serverS = new PeerCont(aConS, dbcSS)
    done()
  })

  it("Restore open tallies", function(done) {
    let dc = sites, _done = () => {if (!--dc) done()}
    dbO.query(defTally.rest(saveName), (e) => {if (e) done(e); else _done()})
    if (sites > 1) dbS.query(defTally.rest(saveName), (e) => {if (e) done(e); _done()})
  })

  it("Initialize DB", function(done) {
    let sql = `begin;
        delete from mychips.chits;
        update mychips.tallies set _last_chit = 0 where tally_ent = %L and status = 'open' returning tally_ent, tally_seq, tally_uuid; commit`
      , dc = 2, _done = () => {if (!--dc) done()}	//dc _done's to be done
    dbO.query(Format(sql, userO), (e, res) => {if (e) done(e)
      assert.equal(res[2].rowCount, 1)
      let row = res[2].rows[0]			//;log.debug('row O:', row)
      assert.equal(row.tally_ent, userO)
      interTest.talO = row
      _done()
    })
    dbS.query(Format(sql, userS), (e, res) => {if (e) done(e)
      assert(res[2].rowCount, 1)
      let row = res[2].rows[0]			//;log.debug('row S:', row)
      assert.equal(row.tally_ent, userS)
      interTest.talS = row
      _done()
    })
  })

  it("Originator requests payment from Subject", function(done) {
    let uuid = mkUuid(cuidO, agentO)
      , seq = interTest.talO.tally_seq
      , value = 1234500
      , ref = {x: 'Consulting invoice'}
      , memo = 'A test memo'
      , request = 'pend'
      , sql = Format(`insert into mychips.chits_v (chit_ent, chit_seq, chit_uuid, chit_type, units, reference, memo, request)
          values (%L, %s, %L, 'tran', %s, %L, %L, %L) returning *`, userO, seq, uuid, value, ref, memo, request)
      , dc = 3, _done = () => {if (!--dc) done()}	//dc _done's to be done
//log.debug("Sql:", sql)
    dbO.query(sql, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.chit_ent, userO)
      assert.equal(row.chit_uuid, uuid)
      assert.equal(row.request, request)
      assert.deepStrictEqual(row.reference, ref)
      assert.equal(row.net_p, 0)
      assert.equal(row.net_g, 0)
      assert.ok(!row.chain_prv)
      assert.ok(!row.chain_idx)
      _done()
    })
    busS.register('ps', (msg) => {		//log.debug("S user msg:", msg)
      assert.equal(msg.state, 'L.pend')		//Subject is notified of the invoice
      let obj = msg.object
      assert.deepStrictEqual(obj.ref, ref)
      assert.equal(obj.units, value)
      assert.equal(obj.tally, interTest.talO.tally_uuid)
      assert.equal(obj.memo, memo)
      assert.equal(obj.uuid, uuid)
      assert.ok(!obj.sign)
      interTest.chitS = obj
      _done()
    })
    busO.register('po', (msg) => {		//log.debug("O user msg:", msg)
      assert.equal(msg.state, 'A.pend')		//Originator is notified of the updated record
      let obj = msg.object
      assert.deepStrictEqual(obj.ref, ref)
      assert.equal(obj.units, value)
      assert.ok(!obj.sign)
      interTest.chitO = obj
      _done()
    })
  })

  it("Save pending chits for later testing", function(done) {
    let dc = sites, _done = () => {if (!--dc) done()}
    dbO.query(save('pend'), (e) => {if (e) done(e); _done()})
    if (sites > 1) dbS.query(save('pend'), (e) => {if (e) done(e); _done()})
  })

  it("Subject declines Originator's invoice", function(done) {
//log.debug("S:", interTest.chitS)
    let uuid = interTest.chitS.uuid
      , sql = uSql('request = %L', 'void', userS, uuid)
      , dc = 3, _done = () => {if (!--dc) done()}	//dc _done's to be done
//log.debug("Sql:", sql)
    dbS.query(sql, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.chit_uuid, uuid)
      assert.equal(row.state, 'L.pend.void')
      _done()
    })
    busS.register('ps', (msg) => {		//log.debug("S user msg:", msg)
      assert.equal(msg.state, 'L.void')
      assert.ok(!msg.object.sign)
      _done()
    })
    busO.register('po', (msg) => {		//log.debug("O user msg:", msg)
      assert.equal(msg.state, 'A.void')
      assert.ok(!msg.object.sign)
      _done()
    })
  })

  it("Originator modifies/resubmits refused invoice", function(done) {
    let uuid = interTest.chitS.uuid
      , memo = 'A revised memo'
      , sql = uSql('request = %L, memo = %L', 'pend', memo, userO, uuid)
      , dc = 3, _done = () => {if (!--dc) done()}	//dc _done's to be done
//log.debug("Sql:", sql)
    dbO.query(sql, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.chit_uuid, uuid)
      assert.equal(row.state, 'A.draft.pend')
      assert.equal(row.memo, memo)
      _done()
    })
    busS.register('ps', (msg) => {		//log.debug("S user msg:", msg)
      assert.equal(msg.state, 'L.pend')
      assert.equal(msg.object.memo, memo)
      _done()
    })
    busO.register('po', (msg) => {		//log.debug("O user msg:", msg)
      assert.equal(msg.state, 'A.pend')
      assert.equal(msg.object.memo, memo)
      _done()
    })
  })

  it("Restore pending chits", function(done) {
    let dc = sites, _done = () => {if (!--dc) done()}
    dbO.query(rest('pend'), (e) => {if (e) done(e); else done()})
    if (sites > 1) dbS.query(rest('pend'), (e) => {if (e) done(e); _done()})
  })

  it("Generate chit signature", function(done) {
    getSignature(dbS, userS, interTest.chitS.uuid, done)
  })

  it("Subject accepts/pays Originator's invoice", function(done) {
    let uuid = interTest.sign.uuid
      , sign = interTest.sign.text
      , sql = uSql('request = %L, signature = %L', 'good', sign, userS, uuid)
      , dc = 3, _done = (x) => {if (!--dc) done()}
//log.debug("Sql:", dc, sql)
    dbS.query(sql, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("Row:", dc, e, row)
      assert.equal(row.chit_uuid, uuid)
      assert.equal(row.state, 'L.pend.good')
      _done('q')
    })
    busS.register('ps', (msg) => {		//log.debug("S User msg:", dc, msg, msg.object)
      assert.equal(msg.state, 'L.good')
      assert.ok(msg.object.sign)
      _done('s')
    })
    busO.register('po', (msg) => {		//log.debug("O User msg1:", dc, msg, msg.object)
      assert.equal(msg.state, 'A.good')
      assert.ok(msg.object.sign)
      _done('o')
    })
  })

  it("Grab originator's signing key", function(done) {
    let sql = 'select user_cmt from mychips.users_v where id = $1'
    dbO.query(sql, [userO], (err, res) => { if (err) done(err)
      let row = getRow(res, 0)				//;log.debug("row:", row)
        , key = row.user_cmt				//;log.debug("key:", key)
        interTest.sign = {key}
        assert.ok(key)
        done()
    })
  })

  it("Create chit signature independant of DB", function(done) {
    let uuid = mkUuid(cuidO, agentO)
      , type = 'tran'
      , by = 'stock'
      , units = 99123
      , ref = {z: 'Partial refund'}
      , memo = 'Thanks!'
      , tally = interTest.talO.tally_uuid
      , date = new Date().toISOString()
      , { key } = interTest.sign
      , core = {by, date, memo, ref, tally, type, uuid, units}	//;log.debug("c:", core)
    crypto.sign(key, core).then(sign => {
      let text = Buffer.from(sign).toString('base64url')
      assert.ok(text)			//;log.debug('sign:', text)
      interTest.sign = {key, sign, text, core}
      done()
    })
  })

  it("Originator sends payment to Subject", function(done) {
    let {sign, text, core} = interTest.sign
      , { by, date, memo, ref, tally, type, uuid, units } = core
      , seq = interTest.talO.tally_seq
      , request = 'good'
      , sql = Format(`insert into mychips.chits_v (chit_ent, chit_seq, chit_uuid, chit_date, chit_type, issuer, units, reference, memo, request, signature)
          values (%L, %s, %L, %L, 'tran', %L, %s, %L, %L, %L, %L) returning *`, userO, seq, uuid, date, by, units, ref, memo, request, text)
      , dc = 3, _done = () => {if (!--dc) done()}	//dc _done's to be done
//log.debug("Sql:", sql)
    dbO.query(sql, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.chit_ent, userO)
      assert.equal(row.chit_uuid, uuid)
      assert.equal(row.units, units)
      assert.equal(row.net, -units)
      assert.equal(row.request, request)
      assert.deepStrictEqual(row.reference, ref)
      _done()
    })
    busS.register('ps', (msg) => {		//log.debug("S user msg:", msg, msg.object)
      assert.equal(msg.state, 'A.good')
      let obj = msg.object
      assert.deepStrictEqual(obj.ref, ref)
      assert.equal(obj.units, units)
      assert.equal(obj.uuid, uuid)
      assert.ok(obj.sign)
      _done()
    })
    busO.register('po', (msg) => {		//log.debug("O user msg:", msg, msg.object)
      assert.equal(msg.state, 'L.good')
      _done()
    })
  })

  it("Wait for consensus to settle", function(done) {setTimeout(done, 250)})

  it("Verify chit consensus in DB", function(done) {
    let sql = `select tally_ent,tally_seq,tally_type,state,chits,chain_conf,ack_hash from mychips.tallies_v where tally_type = $1`
      , dc = 2, _done = () => {if (!--dc) done()}	//dc _done's to be done
    dbO.query(sql, ['stock'], (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("O row:", row)
      assert.equal(row.chits, 2)
      assert.equal(row.chain_conf, 2)
      _done()
    })
    dbS.query(sql, ['foil'], (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("S row:", row)
      assert.equal(row.chits, 2)
      assert.equal(row.chain_conf, 2)
      _done()
    })
  })

  if (saveName) it("Save open chits for later chitcon test", function(done) {
    let dc = sites, _done = () => {if (!--dc) done()}
    dbO.query(save(saveName), (e) => {if (e) done(e); _done()})
    if (sites > 1) dbS.query(save(saveName), (e) => {if (e) done(e); _done()})
  })
  if (saveName) it("Save open tallies for later chitcon test", function(done) {
    let dc = sites, _done = () => {if (!--dc) done()}
    dbO.query(defTally.save(saveName), (e) => {if (e) done(e); _done()})
    if (sites > 1) dbS.query(defTally.save(saveName), (e) => {if (e) done(e); _done()})
  })

  it("Resend good chit", function(done) {
    let uuid = interTest.chitS.uuid
      , sql = uSql('request = %L', 'good', userS, uuid)
//log.debug("Sql:", sql)
    dbS.query(sql, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("Row:", dc, e, row)
      assert.equal(row.state, 'L.good.good')
      done()
    })
  })

  it("Wait for state to settle", function(done) {setTimeout(done, 250)})

  it("Verify chit request field cleared", function(done) {
    let uuid = interTest.chitS.uuid
      , sql = `select request,state from mychips.chits_v where chit_ent = $1 and chit_uuid = $2;`
//log.debug("Sql:", sql)
    dbS.query(sql, [userS, uuid], (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("O row:", row)
      assert.strictEqual(row.request, null)
      assert.equal(row.state, 'L.good')
      done()
    })
  })

/* */
//  it("Mark the log files", function(done) {markLogs(dbO, log, done)})
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{		//Let things flush out before closing
      dbO.disconnect()
      dbS.disconnect()
      serverO.close()
      serverS.close()
      done()
      }, 250)
  })
}		//Suite 1

// Main
// ----------------------------------------------------------------------------
describe("Chit testing", function() {
  let config1 = {		//Two users on name host
    sites:1, saveName:'open1',
    cuidO:cuid0, cuidS:cuid1, userO:user0, userS:user1, aConO:aCon0, aConS:aCon1, agentO:agent0, agentS:agent1,
    dbcO: new dbConf(log, 'mu_p1000'), 
    dbcS: new dbConf(log, 'mu_p1001'),
    dbcSO: new dbConf(),
    dbcSS: new dbConf()
  }
  let config2 = {		//Two users on different hosts
    sites:2, saveName:'open2',
    cuidO:cuid0, cuidS:cuid2, userO:user0, userS:user2, aConO:aCon0, aConS:aCon2, agentO:agent0, agentS:agent2,
    dbcO: new dbConf(log, 'mu_p1000'), 
    dbcS: db2Conf(log, 'mu_p1002'),
    dbcSO: new dbConf(),
    dbcSS: db2Conf()
  }

  describe("Test chits between two users on same site", function() {Suite1(config1)})
  describe("Test chits between two users on different sites", function() {Suite1(config2)})
})

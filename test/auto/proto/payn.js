//Test payment lifts on sample network
//After: netn
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// This simulates lifts on the test network created in netn.js
//TODO:
//- 

const { dbConf, testLog, Format, Bus, assert, mkUuid, getRow, dbClient, libModule, Crypto, peerTest } = require('../common')
const log = testLog(__filename)
const crypto = new Crypto(log)
const clearSql = `begin;
        delete from mychips.chits where chit_type = 'lift';
        delete from mychips.lifts;
        commit;`
const { Sites, initSites } = require('./def-net')
var liftData = [
  ['p1003','p1000', 4],
  ['p1103','p1100', 4],
  ['p1203','p1200', 4],
  ['p1303','p1300', 4],
//  ['p','p', ],
]
var siteData = []
var userData = {}
var interTest = {}			//Pass values from one test to another

const liftPayment = function(dataO, dataS, units, succeed = true) {
  const dbcO = dataO.dConf, cidO = dataO.cid, userO = dataO.id, agentO = dataO.agent
  const dbcS = dataS.dConf, cidS = dataS.cid, userS = dataS.id, agentS = dataS.agent
  const busO = new Bus('busO'), busS = new Bus('busS')
  var dbO, dbS

  before('Connection O to ' + dbcO.dbName, function(done) {	//Emulate originator user
    dbO = new dbClient(dbcO, (chan, data) => {
      log.trace("Notify O on channel:", chan, "data:", data)
      busO.notify(JSON.parse(data))
    }, ()=>{log.info("DB O connection open: " + dbcO.listen); done()})
  })

  before('Connection S to ' + dbcS.dbName, function(done) {	//Emulate subject user
    dbS = new dbClient(dbcS, (chan, data) => {
      log.trace("Notify S on channel:", chan, "data:", data)
      busS.notify(JSON.parse(data))
    }, ()=>{log.info("DB S connection open: " + dbcS.listen); done()})
  })

  it("Grab payor's signing key", function(done) {
    let sql = 'select user_cmt from mychips.users_v where id = $1'
      , parms = [userO]
//log.debug("Sql:", sql, JSON.stringify(parms))
    dbO.query(sql, parms, (err, res) => { if (err) done(err)
      let row = getRow(res, 0)				//;log.debug("row:", row)
        , key = row.user_cmt				//;log.debug("key:", key)
        interTest.sign = { key }
        assert.ok(key)
        done()
    })
  })
  
  it("Create payment signature independant of DB", function(done) {
    let uuid = mkUuid(cidO, agentO)
      , memo = 'Test payment lift'
      , ref = {payee: cidS}
      , find = {cid: cidS, agent: agentS}
      , date = new Date().toISOString()
      , { key } = interTest.sign
      , core = {uuid, find, units, date, memo, ref}	//;log.debug("c:", core)
    crypto.sign(key, core, sign => {
      let text = Buffer.from(sign).toString('base64url')
      assert.ok(text)			//;log.debug('sign:', text)
      interTest.sign = {key, sign, text, core}
      done()
    })
  })

  it("Launch lift payment: " + cidO + " -> " + cidS, function(done) {
    let {sign, text, core} = interTest.sign
      , {uuid, find, units, date, memo, ref} = core
      , auth = {memo, ref, sign:text}
      , sql = `insert into mychips.lifts_v_pay (payor_ent, find, lift_date, units, lift_uuid, payor_auth, request)
	    	values($1,$2,$3,$4,$5,$6,'init') returning *;`
      , parms = [userO, find, date, units, uuid, auth]
      , dc = succeed ? 3 : 2, _done = () => {if (!--dc) done()}	//dc _done's to be done
log.debug("Sql:", sql, JSON.stringify(parms))
    dbO.query(sql, parms, (e, res) => {if (e) done(e)		//;log.debug("Res:", res)
      let pay = getRow(res, 0)					//;log.debug("Pay:", JSON.stringify(pay))
      assert.equal(pay.units, units)
      assert.equal(pay.lift_seq, 0)
      assert.ok(pay.lift_uuid)
      assert.equal(pay.status, 'draft')
      assert.equal(pay.request, 'init')
      assert.deepStrictEqual(pay.payor_auth, auth)
      assert.equal(pay.origin.cid, cidO)
      assert.equal(pay.origin.agent, agentO)
      assert.equal(pay.payee_ent, userS)
      _done()
    })
    busO.register('po', (msg) => {		log.debug("O msg:", msg)
      assert.equal(msg.target, 'lift')
      assert.equal(msg.state, succeed ? 'good' : 'void')
      assert.equal(msg.entity, userO)
      assert.equal(msg.memo, memo)
      assert.deepStrictEqual(msg.ref, ref)
      let obj = msg.object			//;log.debug("A obj:", obj)
      assert.ok(!!obj)				//A tally attached
      assert.equal(obj.units, units)
      _done()
    })
    busS.register('ps', (msg) => {		log.debug("S msg:", msg)
      assert.equal(msg.target, 'lift')
      assert.equal(msg.state, 'good')
      assert.equal(msg.entity, userS)
      assert.equal(msg.memo, memo)
      assert.deepStrictEqual(msg.ref, ref)
      let obj = msg.object			//;log.debug("A obj:", obj)
      assert.ok(!!obj)				//A tally attached
      assert.equal(obj.units, units)
      _done()
    })
  })

/* */
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{		//Let everything flush out before closing
      dbO.disconnect()
      dbS.disconnect()
      done()
      }, 200)
  })

}	//liftPayment

describe("Distributed lift testing", function() {
  initSites(log, siteData, userData)

  siteData.forEach(s => {  
    it('Connect to database ' + s.dbName, function(done) {
      s.db = new dbClient(s.dConf, null, () => {
        log.info("DB connection established:" + s.dbName)
        done()
      })
    })
    it("Clear existing lifts, chits in DB " + s.idx, function(done) {
      s.db.query(clearSql, (e) => {if (e) done(e)
        done()
      })
    })
    it("Launch peer server on " + s.idx, function(done) {
      s.ps = new peerTest(s.aConf, s.dConf)
      done()
    })
  })

  liftData.forEach(l => {
    let [orig, subj, units] = l
    describe("Lift payment: " + orig + " -> " + subj, function() {
      liftPayment(userData[orig], userData[subj], units)
    })  
  })

/*
  it("Launch lift payment that will fail", function(done) {
    let memo = 'Test failed payment lift'
      , ref = {invoice: 5432}
      , sign = user3 + ' ' + cid3 + ' Signature'
      , auth = {memo, ref, sign}
      , units = 5
      , find = {cid: cid0, agent: agent1}
      , sql = `insert into mychips.lifts_v_pay (payor_ent, find, units, payor_auth, request)
	    	values($1,$2,$3,$4,'init') returning *;`
      , parms = [user3, find, units, auth]
      , dc = 2, _done = () => {if (!--dc) done()}	//dc _done's to be done
//log.debug("Sql:", sql, JSON.stringify(parms))
    dbL.query(sql, parms, (e, res) => {if (e) done(e)		//;log.debug("Res:", res)
      let pay = getRow(res, 0)					//;log.debug("Pay:", pay)
      assert.equal(pay.units, units)
      assert.equal(pay.lift_seq, 0)
      assert.equal(pay.status, 'draft')
      assert.equal(pay.request, 'init')
      _done()
    })
    busU.register('pu', (msg) => {		//log.debug("U msg:", msg)
      assert.equal(msg.target, 'lift')
      assert.equal(msg.state, 'void')
      assert.equal(msg.entity, user3)
      _done()
    })
  })

/* */
  after('Disconnect from test databases', function(done) {
    setTimeout(()=>{		//Let everything flush out before closing
      siteData.forEach(s => {
        s.db.disconnect()
        s.ps.close()
      })
      done()
    }, 200)
  })
})

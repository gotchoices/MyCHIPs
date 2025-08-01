//Test payment lifts (OBSOLETE?)
//After: net1 net02
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// This simulates lift across 2 (or three) systems (see doc/uml/test-paths.svg)
//   <-> DB1 <-> Agent1 <-> Agent(0,2) <-> DB2 <->
//
//TODO:
//- Generate payment lift request
//- 

const { dbConf, testLog, Format, Bus, assert, mkUuid, getRow, dbClient, libModule, SubCrypto, peerTest } = require('../common')
const log = testLog(__filename)
const crypto = new SubCrypto(log)
const { host, user0, user1, user2, user3, port0, port1, port2, agent0, agent1, agent2, db2Conf, aCon0, aCon1, aCon2 } = require('../def-users')
const { cuidu, cuidd, cuidb, cuidx, cuidN } = require('./def-path')
const cuid0 = cuidN(0), cuid2 = cuidN(2), cuid3 = cuidN(3)
const adminListen = 'mychips_admin'
const user3Listen = 'mu_' + user3
var interTest = {}			//Pass values from one test to another

describe("Peer-to-peer lift testing", function() {
  var server0, server1, server2
  var busL = new Bus('busL'), busR = new Bus('busR'), busU = new Bus('busU')
  var dbL, dbR, dbU

  before('Connection L to test database', function(done) {
    dbL = new dbClient(new dbConf(log,adminListen), (chan, data) => {
      log.trace("Notify L from channel:", chan, "data:", data)
      busL.notify(JSON.parse(data))
    }, ()=>{log.info("DB connection L established"); done()})
  })

  before('Connection R to test database', function(done) {
    dbR = new dbClient(db2Conf(log,adminListen), (chan, data) => {
      log.trace("Notify R from channel:", chan, "data:", data)
      busR.notify(JSON.parse(data))
    }, ()=>{log.info("DB connection R established"); done()})
  })

  before('User connection to test database', function(done) {
    dbU = new dbClient(new dbConf(log,user3Listen), (chan, data) => {
      log.trace("Notify U from channel:", chan, "data:", data)
      busU.notify(JSON.parse(data))
    }, ()=>{log.info("DB connection U established"); done()})
  })

  before('Launch three peer servers', function(done) {
    server0 = new peerTest(aCon0, db2Conf())
    server1 = new peerTest(aCon1, new dbConf())
    server2 = new peerTest(aCon2, db2Conf())
    done()
  })

  it("Clear local lift chits, init tally lading", function(done) {
    let sql = `delete from mychips.chits where chit_type = 'lift';
               delete from mychips.lifts;
               update mychips.tallies set target = 5 where tally_type = 'foil';
               update mychips.tallies set clutch = 0;`
    dbL.query(sql, (e) => {done(e)})
  })
  
  it("Clear remote lift chits, init tally lading", function(done) {
    let sql = `delete from mychips.chits where chit_type = 'lift';
               delete from mychips.lifts;
               update mychips.tallies set target = 5 where tally_type = 'foil';
               update mychips.tallies set clutch = 0;`
    dbR.query(sql, (e) => {done(e)})
  })

  it("Grab payor's signing key", function(done) {
    let sql = 'select user_cmt from mychips.users_v where id = $1'
      , parms = [user3]
//log.debug("Sql:", sql, JSON.stringify(parms))
    dbL.query(sql, parms, (err, res) => { if (err) done(err)
      let row = getRow(res, 0)				//;log.debug("row:", row)
        , key = row.user_cmt				//;log.debug("key:", key)
        interTest.sign = {key}
        assert.ok(key)
        done()
    })
  })

  it("Create payment signature independant of DB", function(done) {
    let uuid = mkUuid(cuid3, agent1)
      , memo = 'Test payment lift'
      , ref = {invoice: 4321}
      , units = 6
      , find = {cuid: cuid0, agent: agent1}
      , date = new Date().toISOString()
      , { key } = interTest.sign
      , core = {uuid, find, units, date, memo, ref}	//;log.debug("c:", core)
    crypto.sign(key, core).then(sign => {
      let text = Buffer.from(sign).toString('base64url')
      assert.ok(text)			//;log.debug('sign:', text)
      interTest.sign = {key, sign, text, core}
      done()
    })
  })

  it("Launch lift payment to user on same site", function(done) {
    let {sign, text, core} = interTest.sign
      , {uuid, find, units, date, memo, ref} = core
      , auth = {memo, ref, sign:text}
      , sql = `insert into mychips.lifts_v_pay (payor_ent, find, lift_date, units, lift_uuid, payor_auth, request)
	    	values($1,$2,$3,$4,$5,$6,'init') returning *;`
      , parms = [user3, find, date, units, uuid, auth]
      , dc = 3, _done = () => {if (!--dc) done()}	//dc _done's to be done
//log.debug("Sql:", sql, JSON.stringify(parms))
    dbL.query(sql, parms, (e, res) => {if (e) done(e)		//;log.debug("Res:", res)
      let pay = getRow(res, 0)					//;log.debug("Pay:", JSON.stringify(pay))
      assert.equal(pay.units, units)
      assert.equal(pay.lift_seq, 0)
      assert.ok(pay.lift_uuid)
      assert.equal(pay.status, 'draft')
      assert.equal(pay.request, 'init')
      assert.deepStrictEqual(pay.payor_auth, auth)
      assert.equal(pay.origin.cuid, cuid3)
      assert.equal(pay.origin.agent, agent1)
      assert.equal(pay.payee_ent, user0)
//      interTest.p2 = pay
      _done()
    })
    busL.register('pa', (msg) => {		//log.debug("L msg:", msg)
      assert.equal(msg.target, 'tallies')
      assert.equal(msg.oper, 'UPDATE')
      _done()
    })
    busU.register('pu', (msg) => {		//log.debug("U msg:", msg)
      assert.equal(msg.target, 'lift')
      assert.equal(msg.state, 'good')
      assert.equal(msg.entity, user3)
      assert.equal(msg.memo, memo)
      assert.deepStrictEqual(msg.ref, ref)
      let obj = msg.object			//;log.debug("A obj:", obj)
      assert.ok(!!obj)				//A tally attached
      assert.equal(obj.units, units)
      _done()
    })
  })
/*
  it("Launch lift payment that will fail", function(done) {
    let memo = 'Test failed payment lift'
      , ref = {invoice: 5432}
      , sign = user3 + ' ' + cuid3 + ' Signature'
      , auth = {memo, ref, sign}
      , units = 5
      , find = {cuid: cuid0, agent: agent1}
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
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{		//Let everything flush out before closing
      dbL.disconnect()
      dbR.disconnect()
      dbU.disconnect()
      server0.close()
      server1.close()
      server2.close()
      done()
      }, 200)
  })
})

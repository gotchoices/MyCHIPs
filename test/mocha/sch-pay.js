//Test payment lifts schema at a basic level; run
//After: testusers
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// User <-> DB
//TODO:
//-   
const { dbConf, testLog, Format, Bus, assert, getRow, mkUuid, dbClient, queryJson } = require('./common')
var log = testLog(__filename)
const { user0, user1, cid0, cid1, agent0, agent1 } = require('./def-users')
var userListen = 'mu_' + user0
var agentListen = 'ma_' + agent0		//And his agent process
var interTest = {}			//Pass values from one test to another

procSql = function(msg, logic) {
  return Format(`select mychips.lift_process(%L,%L) as ls;`, msg, logic)
}
  
describe("Test payment schema", function() {
  var busU = new Bus('busU'), busA = new Bus('busA')
  var dbU, dbA

  before('User connection to database', function(done) {
    dbU = new dbClient(new dbConf(log,userListen), (chan, data) => {
      log.trace("Notify from U channel:", chan, "data:", data)
      busU.notify(JSON.parse(data))
    }, ()=>{log.info("Test DB user connection established"); done()})
  })

  before('Agent connection to database', function(done) {
    dbA = new dbClient(new dbConf(log,agentListen), (chan, data) => {
      log.trace("Notify from A channel:", chan, "data:", data)
      busA.notify(JSON.parse(data))
    }, ()=>{log.info("Test DB agent connection established"); done()})
  })

  it("Initialize DB", function(done) {
    let sql = `delete from mychips.lifts;`
    dbU.query(sql, (e) => {if (e) done(e); done()})
  })

  it("Can build draft payment record", function(done) {
    let memo = 'Test payment 1'
      , units = 97654
      , payee = {cid: cid1, agent: agent1}
      , sql = `insert into mychips.lifts_v_pay (payor_ent, find, units)
	    	values($1,$2,$3) returning *;`
      , parms = [user0, payee, units]
//log.debug("Sql:", sql, parms)
    dbU.query(sql, parms, (e, res) => {if (e) done(e)		//;log.debug("Res:", res)
      let pay = getRow(res, 0)					//;log.debug("Pay:", pay)
      assert.equal(pay.units, units)
      assert.equal(pay.lift_seq, 0)
      assert.ok(pay.lift_uuid)
      assert.strictEqual(pay.request, null)
      assert.equal(pay.status, 'draft')
      interTest.p1 = pay
      done()
    })
  })

  it("Can build/launch payment record", function(done) {
    let memo = 'Test payment 2'
      , ref = {invoice: 1234}
      , sign = user0 + ' ' + cid0 + ' Signature'
      , auth = {memo, ref, sign}
      , units = 87654
      , find = {cid: cid1, agent: agent1}
      , sql = `insert into mychips.lifts_v_pay (payor_ent, find, units, payor_auth, request)
	    	values($1,$2,$3,$4,'route') returning *;`
      , parms = [user0, find, units, auth]
      , dc = 2, _done = () => {if (!--dc) done()}	//dc _done's to be done
//log.debug("Sql:", sql, parms)
    dbU.query(sql, parms, (e, res) => {if (e) done(e)		//;log.debug("Res:", res)
      let pay = getRow(res, 0)					//;log.debug("Pay:", pay)
      assert.equal(pay.units, units)
      assert.equal(pay.lift_seq, 0)
      assert.ok(pay.lift_uuid)
      assert.equal(pay.status, 'draft')
      assert.equal(pay.request, 'route')
      assert.deepStrictEqual(pay.payor_auth, auth)
      assert.equal(pay.origin.cid, cid0)
      assert.equal(pay.origin.agent, agent0)
      assert.equal(pay.payee_ent, user1)
      interTest.p2 = pay
      _done()
    })
    busA.register('pa', (msg) => {		//Listen for message to agent process
      assert.equal(msg.target, 'lift')		;log.debug("A msg:", msg)
      assert.equal(msg.action, 'route')
      let obj = msg.object			//;log.debug("A obj:", obj)
      assert.ok(!!obj.lift)			//A tally attached
      assert.equal(obj.units, units)
      assert.deepStrictEqual(obj.find, find)
      interTest.m2 = msg			//Save message object
      _done()
    })
  })

  it("Agent evaluates request, confirms change to route (draft.route -> route)", function(done) {
    let msg = interTest.m2
      , { object, sequence } = msg
      , signature = 'Agent signature'
      , logic = {context: ['draft.route'], update: {status: 'route', signature}}
      , sql = 'select mychips.lift_process($1, $2) as status'
      , parms = [msg, logic]
//log.debug("Sql:", sql, parms)
    dbA.query(sql, parms, (e, res) => { if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row?.status, 'route')
      done()
    })
  })

/* */
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{		//Let it flush out before closing
      dbU.disconnect()
      dbA.disconnect()
      done()
      }, 200)
  })
})

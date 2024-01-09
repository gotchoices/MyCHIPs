//Test payment schema at a basic level; run
//After: testusers
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// User <-> DB
//TODO:
//- Test state transitions:
//X-   Can create draft payment
//-   draft -> draft.seek	Request seek for partner
//-   Checks for internal agent, generates local search
//-   Returns path options in payment record
//-   state = seek (or find?)
//-   User can pick route, initiate lift
//-   Lift record is created, committed
//-   payment record: status -> good or void
//-   payment record created for recipient, populated with units, memo, ref
//-   
//- Future
//-   Implement similar for distributed lifts
//- 

const { dbConf, testLog, Format, Bus, assert, getRow, mkUuid, dbClient, queryJson } = require('./common')
var log = testLog(__filename)
//const { user0, port0, port1, port2, agent0, agent1, agent2 } = require('./def-users')
const { user0, user1, cid0, cid1, agent0, agent1 } = require('./def-users')
//const { cidu, cidd, cidN } = require('./def-path')
//var cid0 = cidN(0), cid2 = cidN(2), cid3 = cidN(3), cidb = cidN('B'), cidx = cidN('X')
var userListen = 'mu_' + user0
//var agentListen = 'ma_' + agent1		//And his agent process
//var {save, rest} = require('./def-route')
var interTest = {}			//Pass values from one test to another

describe("Test payment schema", function() {
  var busU = new Bus('busU'), busA = new Bus('busA')
  var dbU, dbA

  before('User connection to database', function(done) {
    dbU = new dbClient(new dbConf(log,userListen), (chan, data) => {
      log.trace("Notify from U channel:", chan, "data:", data)
      busU.notify(JSON.parse(data))
    }, ()=>{log.info("Test DB user connection established"); done()})
  })

//  before('Agent connection to database', function(done) {
//    dbA = new dbClient(new dbConf(log,agentListen), (chan, data) => {
//      log.trace("Notify from A channel:", chan, "data:", data)
//      busA.notify(JSON.parse(data))
//    }, ()=>{log.info("Test DB agent connection established"); done()})
//  })

  it("Initialize DB", function(done) {
    let sql = `begin;
        delete from mychips.pays;
        update mychips.users set _last_pay = 0; commit`
    dbU.query(sql, (e) => {if (e) done(e); done()})
  })

  it("Build draft payment record", function(done) {
    let memo = 'Test payment'
      , reference = {invoice: 1234}
      , units = 97654
      , party = {cid: cid1, agent: agent1}
      , sql = `insert into mychips.pays_v (pay_ent, party, units, memo, reference)
	    	values($1,$2,$3,$4,$5) returning *;`
      , parms = [user0, party, units, memo, reference]
//log.debug("Sql:", sql, parms)
    dbU.query(sql, parms, (e, res) => {if (e) done(e)		//;log.debug("Res:", res)
      let pay = getRow(res, 0)
      assert.strictEqual(pay.lift_uuid, null)
      assert.strictEqual(pay.status, null)
      assert.equal(pay.state, 'draft')
      interTest.p1 = pay
      done()
    })
  })

  it("User requests route to payee", function(done) {
    let sql = `update mychips.pays set request = 'find' where pay_ent = $1 and pay_seq = $2`
      , { pay_ent, pay_seq } = interTest.p1
log.debug("Sql:", sql)
    dbU.query(sql, [pay_ent, pay_seq], (e, res) => { if (e) done(e)
      let row = getRow(res, 0)				;log.debug("row:", row)
//      assert.equal(row.?, 'void')
      done()
    })
  })


/* */
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{		//Let it flush out before closing
      dbU.disconnect()
      done()
      }, 200)
  })
})

//Test lift communications (lib/lift.js); Run only after route, sch-lift
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// This simulates lift across 2 (or three) systems (see doc/uml/test-paths.svg)
//   <-> DB1 <-> Agent1 <-> Agent(0,2) <-> DB2 <->
//
//TODO:
//- Listen for user notifies (are there any)?
//- 
const PeerCont = require("../../lib/peer2peer")
const { dbConf, testLog, Format, Bus, assert, mkUuid, getRow, dbClient, queryJson } = require('./common')
var log = testLog(__filename)
const { host, user0, user1, user2, user3, port0, port1, port2, agent0, agent1, agent2, db2Conf, aCon0, aCon1, aCon2 } = require('./def-users')
const { cidu, cidd, cidb, cidx, cidN } = require('./def-path')
var cid0 = cidN(0), cid2 = cidN(2), cid3 = cidN(3)
var adminListen = 'mychips_admin'
var {save, rest} = require('./def-route')
var interTest = {}			//Pass values from one test to another

describe("Peer-to-peer lift testing", function() {
  var server0, server1, server2
  var busL = new Bus('busL'), busR = new Bus('busR')
  var dbL, dbR

  before('Connection L to test database', function(done) {
    dbL = new dbClient(new dbConf(log,adminListen), (chan, data) => {
      log.trace("Notify L from channel:", chan, "data:", data)
      busL.notify(JSON.parse(data))
    }, ()=>{log.info("DB connection L established"); done()})
  })

  before('User connection R to test database', function(done) {	//Emulate request user
    dbR = new dbClient(db2Conf(log,adminListen), (chan, data) => {
      log.trace("Notify R from channel:", chan, "data:", data)
      busR.notify(JSON.parse(data))
    }, ()=>{log.info("DB connection R established"); done()})
  })

  before('Launch three peer servers', function(done) {
    server0 = new PeerCont(aCon0, db2Conf())
    server1 = new PeerCont(aCon1, new dbConf())
    server2 = new PeerCont(aCon2, db2Conf())
    done()
  })

  it("Clear local lift chits, init tally lading", function(done) {
    let sql = `delete from mychips.chits where chit_type = 'lift';
               delete from mychips.lifts;
               update mychips.routes set min = 2 where status = 'good';
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

  it("Search/create new circuit lift request", function(done) {
    let sql = `select mychips.lift_dist();`
      , dc = 5, _done = () => {if (!--dc) done()}	//_done's to be done
//log.debug("Sql:", sql)
    dbL.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("Q res:", res.rows[0])
      let row = getRow(res, 0)
      assert.equal(row.lift_dist, 1)
      _done()
    })
    busL.register('pl', (msg) => {		//log.debug("L msg:", msg)
      assert.equal(msg.target, 'tallies')	//Capture events (2) when tallies/totals udpated
      assert.equal(msg.oper, 'UPDATE')
      _done()
    })
    busR.register('pr', (msg) => {		//log.debug("R msg:", msg)
      assert.equal(msg.target, 'tallies')	//Two updates on remote site
      assert.equal(msg.oper, 'UPDATE')
      _done()
    })
  })

  it("Create forwardable lift query that will fail to loop back", function(done) {
    let units = 2
      , find = {cid:cidx, agent: agent0}
      , sql = Format(`with
          rr as (select uuids from mychips.routes_v_paths where foro and edges = 1 and inp_cid = %L)
          insert into mychips.lifts (lift_type, circuit, request, units, tallies, find)
          select 'org', true, 'init', %s, rr.uuids, %L from rr returning *;`, cidd, units, find)
      , dc = 8, _done = () => {if (!--dc) done()}	//_done's to be done
//log.debug("Sql:", sql)
    dbR.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("R res:", res.rows[0])
      let row = getRow(res, 0)
      assert.equal(row.request, 'init')
      assert.equal(row.status, 'draft')
      _done()
    })
    busL.register('pl', (msg) => {		//log.debug("L msg:", msg)
      assert.equal(msg.target, 'tallies')	//Capture events (2) when tallies/totals udpated
      assert.equal(msg.oper, 'UPDATE')
      _done()
    })
    busR.register('pr', (msg) => {		//log.debug("R msg:", msg)
      assert.equal(msg.target, 'tallies')	//Six updates on remote site
      assert.equal(msg.oper, 'UPDATE')
      _done()
    })
  })

  it("Wait for messages to settle", function(done) {
    setTimeout(done, 250)
  })

  it("Propagate void messages back around lift loop", function(done) {
    let sql = `update mychips.lifts set status = 'pend', request = 'void'
               where status = 'draft' returning *`
      , dc = 4, _done = () => {if (!--dc) done()}	//_done's to be done
//log.debug("Sql:", sql)
    dbR.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("R res:", res.rows[0])
      let row = getRow(res, 0)
      assert.equal(row.request, 'void')
      assert.equal(row.status, 'pend')
      _done()
    })
    busL.register('pl', (msg) => {		//log.debug("L msg:", msg)
      assert.equal(msg.target, 'tallies')	//Capture events (1) when tallies/totals udpated
      assert.equal(msg.oper, 'UPDATE')
      _done()
    })
    busR.register('pr', (msg) => {		//log.debug("R msg:", msg)
      assert.equal(msg.target, 'tallies')	//Two updates on remote site
      assert.equal(msg.oper, 'UPDATE')
      _done()
    })
  })

/* */
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{		//Let everything flush out before closing
      dbL.disconnect()
      dbR.disconnect()
      server0.close()
      server1.close()
      server2.close()
      done()
      }, 200)
  })
})

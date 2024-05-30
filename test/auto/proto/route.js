//Test route communications (lib/route.js); Run 
//After: net02 sch-route
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
const { dbConf, testLog, Format, Bus, assert, getRow, dbClient, queryJson, libModule } = require('../common')
const PeerCont = require(libModule('peer2peer'))
const log = testLog(__filename)
const { host, user0, user1, user2, user3, port0, port1, port2, agent0, agent1, agent2, db2Conf, aCon0, aCon1, aCon2 } = require('../def-users')
const { cuidu, cuidd, cuidb, cuidx, cuidN } = require('./def-path')
const cuid0 = cuidN(0), cuid2 = cuidN(2), cuid3 = cuidN(3)
const userListenR = 'mu_' + user0
const {save, rest} = require('./def-route')
const routeSql = `select json_agg(s) as json from (
    select rid,via_ent,via_tseq,dst_cuid,dst_agent,status,step,mychips.route_sorter(status,expired) as sorter
    from mychips.routes_v order by rid) s;`
var interTest = {}			//Pass values from one test to another

describe("Peer-to-peer route testing", function() {
  var server0, server1, server2
  var busL = new Bus('busL'), busR = new Bus('busR')
  var dbL, dbR

  before('Connection L to test database', function(done) {
    dbL = new dbClient(new dbConf(log), (chan, data) => {
      log.trace("Notify L from channel:", chan, "data:", data)
      busL.notify(JSON.parse(data))
    }, ()=>{log.info("DB connection L established"); done()})
  })

  before('User connection R to test database', function(done) {	//Emulate request user
    dbR = new dbClient(db2Conf(log, userListenR), (chan, data) => {
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

  it("Clear Local DB routes", function(done) {
    dbL.query('delete from mychips.routes;', (e) => {done(e)})
  })

  it("Initiate route request from cuid_D to cuid_U", function(done) {
    let sql = `with t as
      (select tally_ent as ent, tally_seq as seq from mychips.tallies where tally_type = 'stock' and part_ent isnull)
        insert into mychips.routes_v (via_ent, via_tseq, dst_cuid, dst_agent, req_ent, req_tseq)
          select t.ent, t.seq, $1, $2, t.ent, null from t returning *;`
      , parms = [cuidu, agent0]
      , dc = 2, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql, 'parms', parms)
    dbR.query(sql, parms, (e, res) => {if (e) done(e)	//;log.debug("R res:", res.rows[0])
      let row = getRow(res, 0)
      interTest.r0 = row			//Save original route record
      assert.equal(row.via_ent, user0)
      assert.equal(row.dst_cuid, cuidu)
      assert.equal(row.dst_agent, agent0)
      _done()
    })
    busR.register('pr', (msg) => {		//;log.debug("R msg:", msg)
      assert.equal(msg.target, 'route')
      assert.equal(msg.action, 'good')
      let obj = msg.object			//;log.debug("R obj:", obj, "F:", obj.find)
      assert.equal(obj.find.cuid, cuidu)
      assert.equal(obj.find.agent, agent0)
      _done()
    })
  })

  it("Should produce one good route record remotely", function(done) {
    queryJson('routes_v3', dbR, routeSql, done)
  })

  it("Should produce pend,none route records locally", function(done) {
    setTimeout(()=>{
      queryJson('routes_v4', dbL, routeSql, done)
    }, 200)	//No good way to detect when status has transacted to pend, just wait a bit
  })

  it("Clear Local DB routes", function(done) {
    dbL.query('delete from mychips.routes;', (e) => {done(e)})
  })

  it("Clear Remote DB routes, setup tally capacity", function(done) {
    let sql = `delete from mychips.routes;
               update mychips.tallies set target = 2 where tally_type = 'foil';`
    dbR.query(sql, (e) => {done(e)})
  })

  it("Initiate route request from cuid_D to cuid_X", function(done) {
    let sql = `with t as
      (select tally_ent as ent, tally_seq as seq from mychips.tallies where tally_type = 'stock' and part_ent isnull)
        insert into mychips.routes_v (via_ent, via_tseq, dst_cuid, dst_agent, req_ent, req_tseq)
          select t.ent, t.seq, $1, $2, t.ent, null from t returning *;`
      , parms = [cuidx, agent0]
      , dc = 2, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql, 'parms', parms)
    dbR.query(sql, parms, (e, res) => {if (e) done(e)	//;log.debug("R res:", res.rows[0])
      let row = getRow(res, 0)
      interTest.r0 = row			//Save original route record
      assert.equal(row.via_ent, user0)
      assert.equal(row.dst_cuid, cuidx)
      assert.equal(row.dst_agent, agent0)
      _done()
    })
    busR.register('pr', (msg) => {		//;log.debug("R msg:", msg)
      assert.equal(msg.target, 'route')
      assert.equal(msg.action, 'good')
      let obj = msg.object			//;log.debug("R obj:", obj, "F:", obj.find)
      assert.equal(obj.find.cuid, cuidx)
      assert.equal(obj.find.agent, agent0)
      _done()
    })
  })

  it("Save good route record to X for lift testing", function(done) {
    dbL.query(save('goodX'), (e) => {if (e) done(e); done()})
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

//  after('Inspect event loop', function() {
//    setTimeout(()=>{
//      process._getActiveHandles().forEach(h=>{log.debug("Handle:", h)})
//      process._getActiveRequests().forEach(r=>{log.debug("Request:", r)})
//    }, 1000)
//  })
})

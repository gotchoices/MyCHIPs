//Test route communications (lib/route.js); Run only after sch-route user2
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// This simulates two (nearly/three) systems
//   <-> DB1 <-> Agent1 <-> Agent(0,2) <-> DB2 <->
//
// Will build test tallies in DB2 as follows; see: doc/uml/test-paths.svg
//    Ex-cid_3:agent1 -> u0-cid_D:agent2  >------------------\
//                       u1-cid_U:agent0 -> Ex-cid_0:agent1   |
//    u2-cid_X:agent0 -> u3-cid_B:agent0 -> Ex-cid_2:agent1   |
//           ^-----------------------------------------------/
//
const PeerCont = require("../../lib/peer2peer")
const { dbConf, testLog, Format, Bus, assert, mkUuid, getRow, dbClient, queryJson } = require('./common')
var log = testLog(__filename)
const { host, user0, user1, user2, user3, port0, port1, port2, agent0, agent1, agent2, db2Conf, aCon0, aCon1, aCon2 } = require('./def-users')
const { cidu, cidd, cidb, cidx, cidN } = require('./def-path')
var cid0 = cidN(0), cid2 = cidN(2), cid3 = cidN(3)
var userListenR = 'mu_' + user0
var tallySql = `insert into mychips.tallies (tally_ent, tally_type, tally_uuid, contract, hold_cert, part_cert, hold_sig, part_sig, status) values (%L,%L,%L,%L,%L,%L,%L,%L,'open') returning *`
var agree = {domain:"mychips.org", name:"test", version:1}
var {save, rest} = require('./def-route')
var interTest = {}			//Pass values from one test to another
var routeSql = `select json_agg(s) as json from (
    select rid,via_ent,via_tseq,dst_cid,dst_agent,status,step,mychips.route_sorter(status,expired) as sorter
    from mychips.routes_v order by rid) s;`

describe("Initialize DB2 tally/path test data", function() {
  var dbR, dbL

  before('Connect to L database (from sch-route test)', function(done) {
    dbL = new dbClient(new dbConf(log), null, ()=>{done()})
  })

  it("Grab connecting tallies from L database", function(done) {
    let sql = 'select jsonb_object_agg(part_cid,tally_uuid) as uuids from mychips.tallies_v where part_ent isnull;'
    dbL.query(sql, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("LT uuids:", row.uuids)
      interTest.lTallies = row.uuids
      done()
    })
  })

  before('Connect to new R database', function(done) {
    dbR = new dbClient(db2Conf(log), null, ()=>{done()})
  })

  it("Clear R DB", function(done) {
    let sql = `begin;
        delete from mychips.tallies;
        delete from base.ent where ent_num >= 100;
        update mychips.users set _last_tally = 0;
        alter sequence mychips.routes_rid_seq restart with 1;
        delete from mychips.routes; commit;`
    dbR.query(sql, (e) => {if (e) done(e); done()})
  })

  it("Build remote test users", function(done) {
    let dat = [
        {name:'User D', cid:cidd, agent:agent2, port:port2, host},
        {name:'User U', cid:cidu, agent:agent0, port:port0, host},
        {name:'User X', cid:cidx, agent:agent0, port:port0, host},
        {name:'User B', cid:cidb, agent:agent0, port:port0, host}]
      , dc = dat.length, _done = () => {if (!--dc) done()}	//_done's to be done
      , count = 0
    dat.forEach(d => {
      let { name, cid, agent, host, port} = d
        , sql = `insert into mychips.users_v (ent_name, peer_cid, peer_agent, peer_host, peer_port) values($1, $2, $3, $4, $5) returning *;`
      dbR.query(sql, [name, cid, agent, host, port], (e, res) => {if (e) done(e)
        assert.equal(res.rowCount, 1)
        let row = getRow(res, 0)			//;log.debug("row:", row)
        assert.equal(row.id, 'p' + (1000 + count))
        assert.equal(row.peer_cid, cid)
        assert.equal(row.peer_agent, agent)
        count++
        _done()
      })
    })
  })

  it("Build remote test tallies", function(done) {	//log.debug("lT uuids:", interTest.lTallies)
     let uuidU = interTest.lTallies[cidu]
       , uuidD = interTest.lTallies[cidd]
       , uuidB = interTest.lTallies[cidb]
       , uuid1 = mkUuid(cidx, agent0)
       , uuid2 = mkUuid(cidd, agent2)
       , cert0 = {chad:{cid:cid0, agent:agent1, host, port:port1}}
       , cert2 = {chad:{cid:cid2, agent:agent1, host, port:port1}}
       , cert3 = {chad:{cid:cid3, agent:agent1, host, port:port1}}
       , certU = {chad:{cid:cidu, agent:agent0, host, port:port0}}
       , certD = {chad:{cid:cidd, agent:agent2, host, port:port2}}
       , certB = {chad:{cid:cidb, agent:agent0, host, port:port0}}
       , certX = {chad:{cid:cidx, agent:agent0, host, port:port0}}
       , sig = 'Valid Signature'
     let dat = [
        {id:user0, type:'stock', uuid:uuidD, hCert:certD, pCert:cert3},
        {id:user1, type:'foil',  uuid:uuidU, hCert:certU, pCert:cert0},
        {id:user2, type:'foil',  uuid:uuid1, hCert:certX, pCert:certB},
        {id:user3, type:'stock', uuid:uuid1, hCert:certB, pCert:certX},
        {id:user0, type:'foil',  uuid:uuid2, hCert:certD, pCert:certX},
        {id:user2, type:'stock', uuid:uuid2, hCert:certX, pCert:certD},
        {id:user3, type:'foil',  uuid:uuidB, hCert:certB, pCert:cert2}]
      , dc = dat.length, _done = () => {if (!--dc) done()}
    dat.forEach(d => {
      let { id, type, uuid, hCert, pCert, hSig, pSig } = d
        , sql = Format(tallySql, id, type, uuid, agree, hCert, pCert, sig, sig)
//log.debug("Sql:", sql)
      dbR.query(sql, (e, res) => {if (e) done(e)
        assert.equal(res.rowCount, 1)
        let row = getRow(res, 0)			//;log.debug("row:", row)
        assert.equal(row.tally_uuid.length, 36)
        _done()
      })
    })
  })

/* */
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{		//Let it flush out before closing
      dbR.disconnect()
      dbL.disconnect()
      done()
      }, 200)
  })
})

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

  it("Initiate route request from cid_D to cid_U", function(done) {
    let sql = `with t as
      (select tally_ent as ent, tally_seq as seq from mychips.tallies where tally_type = 'stock' and part_ent isnull)
        insert into mychips.routes_v (via_ent, via_tseq, dst_cid, dst_agent, req_ent, req_tseq)
          select t.ent, t.seq, $1, $2, t.ent, null from t returning *;`
      , parms = [cidu, agent0]
      , dc = 2, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql, 'parms', parms)
    dbR.query(sql, parms, (e, res) => {if (e) done(e)	//;log.debug("R res:", res.rows[0])
      let row = getRow(res, 0)
      interTest.r0 = row			//Save original route record
      assert.equal(row.via_ent, user0)
      assert.equal(row.dst_cid, cidu)
      assert.equal(row.dst_agent, agent0)
      _done()
    })
    busR.register('pr', (msg) => {		//;log.debug("R msg:", msg)
      assert.equal(msg.target, 'route')
      assert.equal(msg.action, 'good')
      let obj = msg.object			//;log.debug("R obj:", obj, "F:", obj.find)
      assert.equal(obj.find.cid, cidu)
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

  it("Initiate route request from cid_D to cid_X", function(done) {
    let sql = `with t as
      (select tally_ent as ent, tally_seq as seq from mychips.tallies where tally_type = 'stock' and part_ent isnull)
        insert into mychips.routes_v (via_ent, via_tseq, dst_cid, dst_agent, req_ent, req_tseq)
          select t.ent, t.seq, $1, $2, t.ent, null from t returning *;`
      , parms = [cidx, agent0]
      , dc = 2, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql, 'parms', parms)
    dbR.query(sql, parms, (e, res) => {if (e) done(e)	//;log.debug("R res:", res.rows[0])
      let row = getRow(res, 0)
      interTest.r0 = row			//Save original route record
      assert.equal(row.via_ent, user0)
      assert.equal(row.dst_cid, cidx)
      assert.equal(row.dst_agent, agent0)
      _done()
    })
    busR.register('pr', (msg) => {		//;log.debug("R msg:", msg)
      assert.equal(msg.target, 'route')
      assert.equal(msg.action, 'good')
      let obj = msg.object			//;log.debug("R obj:", obj, "F:", obj.find)
      assert.equal(obj.find.cid, cidx)
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

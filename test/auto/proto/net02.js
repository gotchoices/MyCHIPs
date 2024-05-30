//Build local network for agent0 and agent 2; Run
//After: net1
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// This simulates two (nearly/three) systems
//   <-> DB1 <-> Agent1 <-> Agent(0,2) <-> DB2 <->
//
// Will build test tallies in DB2 as follows; see: doc/uml/test-paths.svg
//    Ex-cuid_3:agent1 -> u0-cuid_D:agent2  >------------------\
//                        u1-cuid_U:agent0 -> Ex-cuid_0:agent1   |
//    u2-cuid_X:agent0 -> u3-cuid_B:agent0 -> Ex-cuid_2:agent1   |
//           ^-----------------------------------------------/
//
const { dbConf, testLog, Format, Bus, assert, mkUuid, getRow, dbClient, queryJson, libModule } = require('../common')
const PeerCont = require(libModule('peer2peer'))
const log = testLog(__filename)
const { host, user0, user1, user2, user3, port0, port1, port2, agent0, agent1, agent2, db2Conf, aCon0, aCon1, aCon2 } = require('../def-users')
const { cuidu, cuidd, cuidb, cuidx, cuidN } = require('./def-path')
const cuid0 = cuidN(0), cuid2 = cuidN(2), cuid3 = cuidN(3)
const userListenR = 'mu_' + user0
const tallySql = `insert into mychips.tallies (tally_ent, tally_type, tally_uuid, contract, hold_cert, part_cert, hold_sig, part_sig, part_sets, status) values (%L,%L,%L,%L,%L,%L,%L,%L,%L,'open') returning *`
const agree = {domain:"mychips.org", name:"test", version:1}
var interTest = {}			//Pass values from one test to another
require('./net1')

describe("Initialize DB2 tally/path test data", function() {
  var dbR, dbL

  before('Connect to L database (from sch-route test)', function(done) {
    dbL = new dbClient(new dbConf(log), null, ()=>{done()})
  })

  it("Grab connecting tallies from L database", function(done) {
    let sql = 'select jsonb_object_agg(part_cuid,tally_uuid) as uuids from mychips.tallies_v where part_ent isnull;'
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
        {name:'User D', cuid:cuidd, agent:agent2, port:port2, host},
        {name:'User U', cuid:cuidu, agent:agent0, port:port0, host},
        {name:'User X', cuid:cuidx, agent:agent0, port:port0, host},
        {name:'User B', cuid:cuidb, agent:agent0, port:port0, host}]
      , dc = dat.length, _done = () => {if (!--dc) done()}	//_done's to be done
      , count = 0
    dat.forEach(d => {
      let { name, cuid, agent, host, port} = d
        , sql = `insert into mychips.users_v (ent_name, peer_cuid, peer_agent, peer_host, peer_port) values($1, $2, $3, $4, $5) returning *;`
      dbR.query(sql, [name, cuid, agent, host, port], (e, res) => {if (e) done(e)
        assert.equal(res.rowCount, 1)
        let row = getRow(res, 0)			//;log.debug("row:", row)
        assert.equal(row.id, 'p' + (1000 + count))
        assert.equal(row.peer_cuid, cuid)
        assert.equal(row.peer_agent, agent)
        count++
        _done()
      })
    })
  })

  it("Build remote test tallies", function(done) {	//log.debug("lT uuids:", interTest.lTallies)
     let uuidU = interTest.lTallies[cuidu]
       , uuidD = interTest.lTallies[cuidd]
       , uuidB = interTest.lTallies[cuidb]
       , uuid1 = mkUuid(cuidx, agent0)
       , uuid2 = mkUuid(cuidd, agent2)
       , cert0 = {chad:{cuid:cuid0, agent:agent1, host, port:port1}}
       , cert2 = {chad:{cuid:cuid2, agent:agent1, host, port:port1}}
       , cert3 = {chad:{cuid:cuid3, agent:agent1, host, port:port1}}
       , certU = {chad:{cuid:cuidu, agent:agent0, host, port:port0}}
       , certD = {chad:{cuid:cuidd, agent:agent2, host, port:port2}}
       , certB = {chad:{cuid:cuidb, agent:agent0, host, port:port0}}
       , certX = {chad:{cuid:cuidx, agent:agent0, host, port:port0}}
       , sig = 'Valid Signature'
       , pSet = {target: 10, bound: 10}
     let dat = [
        {id:user0, type:'stock', uuid:uuidD, hCert:certD, pCert:cert3, pSet},
        {id:user1, type:'foil',  uuid:uuidU, hCert:certU, pCert:cert0, pSet},
        {id:user2, type:'foil',  uuid:uuid1, hCert:certX, pCert:certB, pSet},
        {id:user3, type:'stock', uuid:uuid1, hCert:certB, pCert:certX, pSet},
        {id:user0, type:'foil',  uuid:uuid2, hCert:certD, pCert:certX, pSet},
        {id:user2, type:'stock', uuid:uuid2, hCert:certX, pCert:certD, pSet},
        {id:user3, type:'foil',  uuid:uuidB, hCert:certB, pCert:cert2, pSet}]
      , dc = dat.length, _done = () => {if (!--dc) done()}
    dat.forEach(d => {
      let { id, type, uuid, hCert, pCert, hSig, pSig, pSet } = d
        , sql = Format(tallySql, id, type, uuid, agree, hCert, pCert, sig, sig, pSet)
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

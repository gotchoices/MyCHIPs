//Test local pathway schema at a basic level; run after impexp
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// This will build a network of tallies as follows: (see doc/uml/test-paths.svg)
//                              ________(-)_______
//                             ^                  v
//  External_Up -> User_0 -> User_1 -> User_2 -> User_3 -> External_Down
//                   ^____________________v
//TODO:
//- 
const { dbConf, testLog, Format, Bus, assert, getRow, mkUuid, dbClient, queryJson } = require('./common')
var log = testLog(__filename)
//const Serialize = require("json-stable-stringify")
const { host, port0, port1, port2, agent0, agent1, agent2 } = require('./def-users')
const { cidu, cidd, cidN } = require('./def-path')
var interTest = {}			//Pass values from one test to another
var tallySql = `insert into mychips.tallies (tally_ent, tally_uuid, tally_date, tally_type, contract, hold_cert, part_cert, hold_sig, part_sig, status) values (%L,%L,%L,%L,%L,%L,%L,%L,%L,'open') returning *`
var chitSql = `insert into mychips.chits (chit_ent, chit_seq, chit_uuid, units, signature, reference, status) select %L,%s,%L,%s,%L,%L,'good'`
var agree = {domain:"mychips.org", name:"test", version:1}
var users = 4

describe("Initialize tally/path test data", function() {
  var db

  before('Connect to database', function(done) {
    db = new dbClient(new dbConf(log), null, ()=>{
      log.info("Test DB user connection established"); done()}
    )
  })

  it("Clear DB", function(done) {
    let sql = `begin;
        delete from mychips.tallies;
        delete from base.ent where ent_num >= 100;
        update mychips.users set _last_tally = 0; commit`
    db.query(sql, (e) => {if (e) done(e); done()})
  })

  it("Build users: " + users, function(done) {
    let dc = users, _done = () => {if (!--dc) done()}	//_done's to be done
    for (let u = 0; u < users; u++) {
      let cid = cidN(u)
        , name = "User " + u
        , sql = `insert into mychips.users_v (ent_name, peer_cid, peer_agent, peer_host, peer_port) values($1, $2, $3, $4, $5) returning *;`
      db.query(sql, [name, cid, agent1, host, port1], (e, res) => {if (e) done(e)
        assert.equal(res.rowCount, 1)
        let row = res.rows[0]				//;log.debug('row:', row)
        assert.equal(row.id, 'p' + (1000 + u))
        assert.equal(row.peer_cid, cid)
        assert.equal(row.peer_agent, agent1)
        _done()
      })
    }
  })

  it(`Build local tallies between ${users} users`, function(done) {
    let dc = users-1, _done = () => {if (!--dc) done()}
    interTest.ids = []
    for (let u = 1; u < users; u++) {
      let s = u, f = u-1
        , sCid = cidN(s), fCid = cidN(f)
        , tuid = mkUuid(sCid, agent1), cuid = mkUuid(fCid, agent1)
        , date = new Date().toISOString()
        , sId = 'p' + (1000+s), fId = 'p' + (1000+f)
        , sCert = {chad:{cid:sCid, agent:agent1, host, port:port1}}
        , fCert = {chad:{cid:fCid, agent:agent1, host, port:port1}}
        , sSig = sCid + ' signature', fSig = fCid + ' signature'
        , units = u * 2
        , sql = `
          with t as (${Format(tallySql, sId, tuid, date, 'stock', agree, sCert, fCert, sSig, fSig)})
               ${Format(chitSql, sId, 't.tally_seq', cuid, units, sSig, u)} from t returning *;
          with t as (${Format(tallySql, fId, tuid, date, 'foil', agree, fCert, sCert, fSig, sSig)})
               ${Format(chitSql, fId, 't.tally_seq', cuid, units, fSig, u)} from t returning *;`
//log.debug('sql:', sql)
      db.query(sql, (e, res) => {if (e) done(e)		//;log.debug('res:', res)
        assert.equal(res.length, 2)
        let [ res0, res1 ] = res			//;log.debug('r:', res0, res1)
        assert.equal(res0.rowCount, 1)
        assert.equal(res1.rowCount, 1)
        let row0 = res0.rows[0], row1 = res1.rows[0]	//;log.debug('r:', row0, row1)
        assert.equal(row0.chit_uuid, cuid)
        assert.equal(row1.chit_uuid, cuid)
        _done()
      })
      interTest.ids[u] = {sId, fId, sCid, fCid, sCert, fCert, sSig, fSig}	//Save for future tests
    }
  })

  it("Build up-stream foreign tally", function(done) {
    let s= interTest.ids[1]
      , sId = s.fId, sCid = s.fCid, sCert = s.fCert, sSig = s.fSig
      , fCid = cidu
      , tuid = mkUuid(sCid, agent1), cuid = mkUuid(fCid, agent1)
      , date = new Date().toISOString()
      , fCert = {chad:{cid:fCid, agent:agent0, host, port:port0}}
      , fSig = fCid + ' signature'
      , units = users * 2
      , sql = `with t as (${Format(tallySql, sId, tuid, date, 'stock', agree, sCert, fCert, sSig, fSig)})
          ${Format(chitSql, sId, 't.tally_seq', cuid, units, sSig, users)} from t returning *;`
    db.query(sql, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.chit_uuid, cuid)
      done()
    })
  })

  it("Build down-stream foreign tally", function(done) {
    let f= interTest.ids[users-1]
      , fId = f.sId, fCid = f.sCid, fCert = f.sCert, fSig = f.sSig
      , sCid = cidd
      , tuid = mkUuid(sCid, agent1), cuid = mkUuid(fCid, agent1)
      , date = new Date().toISOString()
      , sCert = {chad:{cid:sCid, agent:agent2, host, port:port2}}
      , sSig = sCid + ' signature'
      , units = users * 2 + 2
      , sql = `with t as (${Format(tallySql, fId, tuid, date, 'foil', agree, fCert, sCert, fSig, sSig)})
          ${Format(chitSql, fId, 't.tally_seq', cuid, units, fSig, users+1)} from t returning *;`
    db.query(sql, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.chit_uuid, cuid)
      done()
    })
  })

  it("Build loop-back internal tallies", function(done) {
    let dc = 2, _done = () => {if (!--dc) done()}
      , buildem = (sId, sCid, sCert, sSig, fId, fCid, fCert, fSig, u, units) => {
         let tuid = mkUuid(sCid, agent0), cuid = mkUuid(fCid, agent0)
           , date = new Date().toISOString()
           , sql = `
               with t as (${Format(tallySql, sId, tuid, date, 'stock', agree, sCert, fCert, sSig, fSig)})
                    ${Format(chitSql, sId, 't.tally_seq', cuid, units, sSig, u)} from t returning *;
               with t as (${Format(tallySql, fId, tuid, date, 'foil', agree, fCert, sCert, fSig, sSig)})
                    ${Format(chitSql, fId, 't.tally_seq', cuid, units, fSig, u)} from t returning *;`
//log.debug('sql:', sql)
          db.query(sql, (e, res) => {if (e) done(e)	//;log.debug('res:', res)
            assert.equal(res.length, 2)
            let [ res0, res1 ] = res			//;log.debug('r:', res0, res1)
            assert.equal(res0.rowCount, 1)
            assert.equal(res1.rowCount, 1)
            let row0 = res0.rows[0], row1 = res1.rows[0]	//;log.debug('r:', row0, row1)
            assert.equal(row0.chit_uuid, cuid)
            assert.equal(row1.chit_uuid, cuid)
            _done()
          })
        }
    let x = interTest.ids[1], y = interTest.ids[users-1]
    buildem (y.sId, y.sCid, y.sCert, y.sSig, x.sId, x.sCid, x.sCert, x.sSig, users+2, -(users*2+4))
    buildem (x.fId, x.fCid, x.fCert, x.fSig, y.fId, y.fCid, y.fCert, y.fSig, users+3, users*2+6)
  })

  it("Check view tallies_v_net", function(done) {
    let sql = `update mychips.tallies set target = 3, bound = 7;
               select json_agg(s) as json from (select tally_ent,tally_seq,tally_type,inv,inp,out,target,bound,net_pc,min,max,sign
               from mychips.tallies_v_net order by 1,2,3,4) s;`
    queryJson('tallies_v_net', db, sql, done, 2)
  })

  it("Check view tallies_v_paths", function(done) {
    let sql = `
        update mychips.tallies set reward = 0.02, clutch = 0.04 where tally_type = 'foil';
        update mychips.tallies set reward = 0.04, clutch = 0.001 where tally_type = 'stock';
        select json_agg(s) as json from (
          select inp,out,circuit,min,max,bang,reward,margin,ath
            from mychips.tallies_v_paths where min > 0 and edges > 1 order by path) s;`
    queryJson('tallies_v_paths', db, sql, done, 3)
  })

/* */
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{db.disconnect(); done()}, 200)
  })
})

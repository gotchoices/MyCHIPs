//Build local network for agent1
//After: ../schema/dbinit
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// This will build a network of tallies as follows: (see doc/uml/test-paths.svg)
//                              ________(-)_______
//                             ^                  v
//  External_Up -> User_0 -> User_1 -> User_2 -> User_3 -> External_Down
//                   ^____________________v
//TODO:
//- Digitally sign tallies?
//- 
const { dbConf, testLog, Format, Bus, assert, getRow, mkUuid, dbClient, queryJson, Crypto } = require('../common')
const log = testLog(__filename)
const crypto = new Crypto()
const { host, port0, port1, port2, agent0, agent1, agent2 } = require('../def-users')
const { cuidu, cuidd, cuidN } = require('./def-path')
const tallySql = `insert into mychips.tallies (tally_ent, tally_uuid, tally_date, tally_type, contract, hold_cert, part_cert, hold_sig, part_sig, status) values (%L,%L,%L,%L,%L,%L,%L,%L,%L,'open') returning *`
const chitSql = `insert into mychips.chits (chit_ent, chit_seq, chit_uuid, units, signature, reference, status) select %L,%s,%L,%s,%L,%L,'good'`
var agree = {domain:"mychips.org", name:"test", version:1}
var users = 4
var interTest = {}			//Pass values from one test to another

describe("Initialize tally/path test data for agent1", function() {
  var db

  before('Connect to database', function(done) {
    db = new dbClient(new dbConf(log), null, ()=>{
      log.info("Test DB user connection established"); done()}
    )
  })

  it("Clear existing DB data", function(done) {
    let sql = `begin;
        delete from mychips.tallies;
        delete from base.ent where ent_num >= 100;
        update mychips.users set _last_tally = 0; commit`
    db.query(sql, (e) => {if (e) done(e); done()})
  })

  it("Build users: " + users, function(done) {
    let dc = users, _done = () => {if (!--dc) done()}	//_done's to be done
    for (let u = 0; u < users; u++) {
      let cuid = cuidN(u)
        , name = "User " + u
        , sql = `insert into mychips.users_v (ent_name, peer_cuid, peer_agent, peer_host, peer_port, user_cmt) values($1, $2, $3, $4, $5, $6) returning *;`
      crypto.generate((keyPair, prv, pub) => {
        db.query(sql, [name, cuid, agent1, host, port1, prv], (e, res) => {if (e) done(e)
          assert.equal(res.rowCount, 1)
          let row = res.rows[0]				//;log.debug('row:', row)
          assert.equal(row.id, 'p' + (1000 + u))
          assert.equal(row.peer_cuid, cuid)
          assert.equal(row.peer_agent, agent1)
          _done()
        })
      })
    }
  })

  it(`Build local tallies between ${users} users`, function(done) {
    let dc = users-1, _done = () => {if (!--dc) done()}
    interTest.ids = []
    for (let u = 1; u < users; u++) {
      let s = u, f = u-1
        , sCuid = cuidN(s), fCuid = cuidN(f)
        , tuid = mkUuid(sCuid, agent1), cuid = mkUuid(fCuid, agent1)
        , date = new Date().toISOString()
        , sId = 'p' + (1000+s), fId = 'p' + (1000+f)
        , sCert = {chad:{cuid:sCuid, agent:agent1, host, port:port1}}
        , fCert = {chad:{cuid:fCuid, agent:agent1, host, port:port1}}
        , sSig = sCuid + ' signature', fSig = fCuid + ' signature'
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
      interTest.ids[u] = {sId, fId, sCuid, fCuid, sCert, fCert, sSig, fSig}	//Save for future tests
    }
  })

  it("Build up-stream foreign tally", function(done) {
    let s= interTest.ids[1]
      , sId = s.fId, sCuid = s.fCuid, sCert = s.fCert, sSig = s.fSig
      , fCuid = cuidu
      , tuid = mkUuid(sCuid, agent1), cuid = mkUuid(fCuid, agent1)
      , date = new Date().toISOString()
      , fCert = {chad:{cuid:fCuid, agent:agent0, host, port:port0}}
      , fSig = fCuid + ' signature'
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
      , fId = f.sId, fCuid = f.sCuid, fCert = f.sCert, fSig = f.sSig
      , sCuid = cuidd
      , tuid = mkUuid(sCuid, agent1), cuid = mkUuid(fCuid, agent1)
      , date = new Date().toISOString()
      , sCert = {chad:{cuid:sCuid, agent:agent2, host, port:port2}}
      , sSig = sCuid + ' signature'
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
      , buildem = (sId, sCuid, sCert, sSig, fId, fCuid, fCert, fSig, u, units) => {
         let tuid = mkUuid(sCuid, agent0), cuid = mkUuid(fCuid, agent0)
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
    buildem (y.sId, y.sCuid, y.sCert, y.sSig, x.sId, x.sCuid, x.sCert, x.sSig, users+2, -(users*2+4))
    buildem (x.fId, x.fCuid, x.fCert, x.fSig, y.fId, y.fCuid, y.fCert, y.fSig, users+3, users*2+6)
  })

/* */
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{db.disconnect(); done()}, 200)
  })
})

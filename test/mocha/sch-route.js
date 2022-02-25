//Test route schema at a basic level
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// User <-> DB <-> Agent
// This will build a network of tallies as follows:
//                              ________(-)_______
//                             ^                  v
//  External_Up -> User_0 -> User_1 -> User_2 -> User_3 -> External_Down
//                   ^____________________v
//TODO:
//- 
const { dbConf, Log, Format, Bus, assert, getRow, mkUuid } = require('../settings')
var log = Log('testSchRoute')
var { dbClient } = require("wyseman")
//const Serialize = require("json-stable-stringify")
const { host, port0, port1, agent0, agent1, agent2 } = require('./def-users')
//var userListen = 'mychips_user_' + user0
//var agentListen = 'mychips_agent_' + agent0		//And his agent process
//var {stateField, uSql, save, rest} = require('./def-tally')
var interTest = {}			//Pass values from one test to another
var tallySql = `insert into mychips.tallies (tally_ent, tally_uuid, tally_date, tally_type, contract, hold_cert, part_cert, hold_sig, part_sig, status) values (%L,%L,%L,%L,%L,%L,%L,%L,%L,'open') returning *`
var chitSql = `insert into mychips.chits (chit_ent, chit_seq, chit_uuid, units, signature, quidpro, status) select %L,%s,%L,%s,%L,%L,'good'`
var agree = {domain:"mychips.org", name:"test", version:1}
var users = 4

describe("Initialize route test data", function() {
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
    let dc = users; _done = () => {if (!--dc) done()}	//_done's to be done
    for (let u = 0; u < users; u++) {
      let cid = "cid_" + u
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

  it("Build local tallies", function(done) {
    let dc = users-1; _done = () => {if (!--dc) done()}	//_done's to be done
    interTest.ids = []
    for (let u = 1; u < users; u++) {
      let s = u, f = u-1
        , sCid = 'cid_' + s, fCid = 'cid_' + f
        , tuid = mkUuid(sCid, agent1), cuid = mkUuid(fCid, agent1)
        , date = new Date().toISOString()
        , sId = 'p' + (1000+s), fId = 'p' + (1000+f)
        , sCert = {chad:{cid:sCid, agent:agent1}}, fCert = {chad:{cid:fCid, agent:agent1}}
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

  it("Build up-stream tally", function(done) {
    let s= interTest.ids[1]
      , sId = s.fId, sCid = s.fCid, sCert = s.fCert, sSig = s.fSig
      , fCid = 'cid_U'
      , tuid = mkUuid(sCid, agent1), cuid = mkUuid(fCid, agent1)
      , date = new Date().toISOString()
      , fCert = {chad:{cid:fCid, agent:agent0}}
      , fSig = fCid + ' signature'
      , units = users * 2
      , sql = `with t as (${Format(tallySql, sId, tuid, date, 'stock', agree, sCert, fCert, sSig, fSig)})
          ${Format(chitSql, sId, 't.tally_seq', cuid, units, sSig, users)} from t returning *;`
    db.query(sql, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row);
      assert.equal(row.chit_uuid, cuid)
      done()
    })
  })

  it("Build down-stream tally", function(done) {
    let f= interTest.ids[users-1]
      , fId = f.sId, fCid = f.sCid, fCert = f.sCert, fSig = f.sSig
      , sCid = 'cid_D'
      , tuid = mkUuid(sCid, agent1), cuid = mkUuid(fCid, agent1)
      , date = new Date().toISOString()
      , sCert = {chad:{cid:sCid, agent:agent2}}
      , sSig = sCid + ' signature'
      , units = users * 2 + 2
      , sql = `with t as (${Format(tallySql, fId, tuid, date, 'foil', agree, fCert, sCert, fSig, sSig)})
          ${Format(chitSql, fId, 't.tally_seq', cuid, units, fSig, users+1)} from t returning *;`
    db.query(sql, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row);
      assert.equal(row.chit_uuid, cuid)
      done()
    })
  })

  it("Build loop-back tallies", function(done) {
    let dc = 2; _done = () => {if (!--dc) done()}	//_done's to be done
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
    let expect = [
      {"inp":"p1002", "out":"p1003", "target":3, "bound":7, "units_pc":6,  "min":0,  "max":1,  "sign":1},
      {"inp":"p1001", "out":"p1002", "target":3, "bound":7, "units_pc":4,  "min":0,  "max":3,  "sign":1},
      {"inp":"p1000", "out":"p1001", "target":3, "bound":7, "units_pc":2,  "min":1,  "max":5,  "sign":1},
      {"inp":"p1001", "out":"p1000", "target":3, "bound":7, "units_pc":2,  "min":5,  "max":9,  "sign":-1},
      {"inp":"p1002", "out":"p1001", "target":3, "bound":7, "units_pc":4,  "min":7,  "max":11, "sign":-1},
      {"inp":"p1000", "out":null,    "target":0, "bound":0, "units_pc":8,  "min":8,  "max":8,  "sign":-1},
      {"inp":"p1003", "out":"p1002", "target":3, "bound":7, "units_pc":6,  "min":9,  "max":13, "sign":-1},
      {"inp":null,    "out":"p1003", "target":3, "bound":7, "units_pc":10, "min":13, "max":17, "sign":-1},
      {"inp":"p1001", "out":"p1003", "target":3, "bound":7, "units_pc":-12,"min":15, "max":19, "sign":1},
      {"inp":"p1000", "out":"p1002", "target":3, "bound":7, "units_pc":14, "min":17, "max":21, "sign":-1}]
      , sql = `update mychips.tallies set target = 3, bound = 7;
               select json_agg(s) as json from (select inp,out,target,bound,units_pc,min,max,sign from mychips.tallies_v_net order by min,max,sign) s;`
//log.debug("Sql:", sql)
    db.query(sql, null, (e, res) => {if (e) done(e)
      assert.equal(res.length, 2)
      let res1 = res[1]					//;log.debug('res1:', res1)
      assert.equal(res1.rowCount, 1)
      let row = res1.rows[0]				//;log.debug('row:', JSON.stringify(row.json))
      assert.deepStrictEqual(row.json, expect)
      done()
    })
  })

/*
*/
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{db.disconnect(); done()}, 200)
  })
});

describe("Test route state transitions", function() {
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

/*
  it("User request to promote tally to offer (draft -> draft.offer)", function(done) {
    let sql = uSql(`request = 'offer', hold_sig = '${cid0 + ' signature'}'`, user0, 1)
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
//log.debug("Sql:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'draft.offer')
      _done()
    })
    busA.register('pa', (msg) => {		//Listen for message to agent process
      assert.equal(msg.target, 'tally')
      assert.equal(msg.action, 'offer')
      let obj = msg.object			//;log.debug("A obj:", obj)
      assert.ok(!!obj)
      assert.ok(!!obj.uuid)			//A tally attached
      interTest = msg				//Save original tally object
log.debug("Object:", msg.object)
      busA.register('pa')
      _done()
    })
  })

  it("Agent transmits, confirms change to offer (draft.offer -> H.offer)", function(done) {
    let logic = {context: ['draft.offer'], update: {status: 'offer'}}
      , { cid, agent } = interTest.from
      , msg = {to: {cid, agent}, object: interTest.object}
      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'H.offer')
      done()
    })
  })

  it("Save userProffer tally record for later testing", function(done) {
    dbA.query(save('Hoffer'), (e) => {if (e) done(e); else done()})
  })

  var peerProfferGo = function(done) {
    let sign = {foil: cid1 + ' signature', stock:null}		//Altered and signed
      , object = Object.assign({}, interTest.object, {sign})
      , logic = {context: ['null','void','H.offer','P.offer'], upsert: true}
      , { cid, agent } = interTest.from
      , msg = {to: {cid, agent}, object}
      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'P.offer')
      done()
    })
  }

  it("Agent receives alternative draft (H.offer -> P.offer)", function(done) {peerProfferGo(done)})
  
  it("User request to promote tally to offer (P.offer -> P.offer.void)", function(done) {
    let sql = uSql(`request = 'void', hold_sig = null`, user0, 1)
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
//log.debug("Sql:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'P.offer.void')
      _done()
    })
    busA.register('pa', (msg) => {		//Listen for message to agent process
//log.debug("sign:", msg.object.sign)
      assert.equal(msg.target, 'tally')
      assert.equal(msg.action, 'void')
      busA.register('pa')
      _done()
    })
  })

  it("Agent transmits, confirms change to void (P.offer.void -> void)", function(done) {
    let logic = {context: ['P.offer.void'], update: {status: 'void'}}
      , { cid, agent } = interTest.from
      , msg = {to: {cid, agent}, object: interTest.object}
      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'void')
      done()
    })
  })

  it("Save void tally record for later testing", function(done) {
    dbA.query(save('void'), (e) => {if (e) done(e); else done()})
  })

  it("Delete tally", function(done) {
    let sql = `delete from mychips.tallies;`
    dbU.query(sql, (e, res) => {if (e) done(e); else done()})
  })
  it("Agent receives signed offer (<ex nihilo> -> P.offer)", function(done) {peerProfferGo(done)})

  it("Restore void tally", function(done) {
    dbA.query(rest('void'), (e) => {if (e) done(e); else done()})
  })
  it("Agent receives alternative draft (void -> P.offer)", function(done) {peerProfferGo(done)})

  it("Save peerProffer tally record for later testing", function(done) {
    dbA.query(save('Poffer'), (e) => {if (e) done(e); else done()})
  })

  it("Restore H.offer tally", function(done) {
    dbA.query(rest('Hoffer'), (e) => {if (e) done(e); else done()})
  })

  it("Peer rejects tally (H.offer -> void)", function(done) {
    let object = Object.assign({}, interTest.object)
      , logic = {context: ['H.offer'], update: {status: 'void'}}
      , { cid, agent } = interTest.from
      , msg = {to: {cid, agent}, object}
      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'void')
      done()
    })
  })

  it("Restore H.offer tally", function(done) {
    dbA.query(rest('Hoffer'), (e) => {if (e) done(e); else done()})
  })

  it("Peer accepts tally (H.offer -> open)", function(done) {
    let sign = Object.assign({}, interTest.object.sign, {foil: cid1 + ' signature'})
      , object = Object.assign({}, interTest.object, {sign})
      , logic = {context: ['H.offer'], upsert: true, update: {status: 'open'}}
      , { cid, agent } = interTest.from
      , msg = {to: {cid, agent}, object}
      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'open')
      done()
    })
  })

  it("Restore P.offer tally", function(done) {
    dbA.query(rest('Poffer'), (e) => {if (e) done(e); else done()})
  })
  it("User modifies peer draft (P.offer -> draft.offer)", function(done) {
    let sql = uSql(`request = 'offer', hold_sig = '${cid0 + ' signature'}', comment = 'A special condition'`, user0, 1)
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
//log.debug("Sql:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
//log.debug("X:", row.request, row.status, row.hold_sig, row.part_sig)
      assert.equal(row.state, 'draft.offer')
      _done()
    })
    busA.register('pa', (msg) => {		//Listen for message to agent process
      assert.equal(msg.target, 'tally')
      assert.equal(msg.action, 'offer')
      busA.register('pa')
      _done()
    })
  })

  it("Restore P.offer tally", function(done) {
    dbA.query(rest('Poffer'), (e) => {if (e) done(e); done()})
  })

  it("User request to accept draft (P.offer -> B.offer.open)", function(done) {
    let sql = uSql(`request = 'open', hold_sig = '${cid0 + ' signature'}'`, user0, 1)	//Force chips cache to non-zero
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
//log.debug("Sql M:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'B.offer.open')
      _done()
    })
    busA.register('pa', (msg) => {		//Listen for message to agent process
      assert.equal(msg.target, 'tally')
      assert.equal(msg.action, 'open')
      busA.register('pa')
      _done()
    })
  })

  it("Agent transmits, confirms change to open (B.offer.open -> open)", function(done) {
    let logic = {context: ['B.offer.open'], update: {status: 'open'}}
      , { cid, agent } = interTest.from
      , msg = {to: {cid, agent}, object: interTest.object}
      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'open')
      done()
    })
  })

  it("Save open tally record for later testing", function(done) {
    dbA.query(save('open'), (e) => {if (e) done(e); else done()})
  })

  it("User request to close tally (open -> open.close)", function(done) {
    let sql = uSql(`request = 'close'`, user0, 1)
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
//log.debug("Sql M:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'open.close')
      _done()
    })
    busA.register('pa', (msg) => {		//Listen for message to agent process
      assert.equal(msg.target, 'tally')
      assert.equal(msg.action, 'close')
      busA.register('pa')
      _done()
    })
  })

  it("Agent transmits, confirms change to close (open.close -> close)", function(done) {
    let logic = {context: ['open.close'], update: {status: 'close'}}
      , { cid, agent } = interTest.from
      , msg = {to: {cid, agent}, object: interTest.object}
      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'close')
      done()
    })
  })

  it("Restore open tally", function(done) {
    dbA.query(rest('open'), (e) => {if (e) done(e); else done()})
  })
  it("Peer requests tally close (open -> close)", function(done) {
    let object = {uuid: interTest.object.uuid}		//Minimal object
      , logic = {context: ['open'], update: {status: 'close'}}
      , { cid, agent } = interTest.from
      , msg = {to: {cid, agent}, object}
      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'close')
      done()
    })
  })

*/
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{		//Let it flush out before closing
      dbU.disconnect()
      dbA.disconnect()
      done()
      }, 200)
  })
});

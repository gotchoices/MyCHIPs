//Test route schema at a basic level; run after sch-path
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// User <-> DB <-> Agent
//TODO:
//- 
const { dbConf, testLog, Format, Bus, assert, getRow, mkUuid, dbClient, queryJson } = require('./common')
var log = testLog(__filename)
const { host, user0, user1, user2, user3, port0, port1, port2, agent0, agent1, agent2 } = require('./def-users')
const { cidu, cidd, cidN } = require('./def-path')
var cid1 = cidN(1), cid0 = cidN(0), cid2 = cidN(2), cid3 = cidN(3), cida = cidN('A'), cidb = cidN('B'), cidx = cidN('X')
var userListen = 'mu_' + user3
var agentListen = 'ma_' + agent1		//And his agent process
var {save, rest} = require('./def-route')
var queryLogic = {context: ['null','none','pend.X','good.X'], query: true}
var interTest = {}			//Pass values from one test to another
var routeSql = `select json_agg(s) as json from (
    select rid,via_ent,via_tseq,dst_cid,dst_agent,status,step,mychips.route_sorter(status,expired) as sorter
    from mychips.routes_v order by rid) s;`

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

  it("Clear routes in DB", function(done) {
    let sql = `begin;
        delete from mychips.routes;
        alter sequence mychips.routes_rid_seq restart with 1; commit;`
    dbA.query(sql, (e) => {if (e) done(e); done()})
  })

  it("Create new external request draft route (<start> -> draft)", function(done) {
    let sql = `with
          inp as (select tally_ent as ent, tally_seq as seq from mychips.tallies where tally_type = 'stock' and part_ent isnull),
          dst as (select tally_ent as ent, tally_seq as seq, part_cid as cid, part_agent as agent from mychips.tallies where tally_type = 'foil' and part_ent isnull)
        insert into mychips.routes_v (via_ent, via_tseq, dst_cid, dst_agent, req_ent, req_tseq)
          select inp.ent, inp.seq, dst.cid, dst.agent, dst.ent, dst.seq from inp,dst returning *;`
      , dc = 2, _done = () => {if (!--dc) done()}	//_done's to be done
//log.debug("Sql:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("Q res:", res.rows[0])
      let row = getRow(res, 0)
      interTest.r0 = row			//Save original route record
      assert.equal(row.via_ent, user0)
      assert.equal(row.req_ent, user3)
      assert.equal(row.dst_cid, cidd)
      assert.equal(row.dst_agent, agent2)
      assert.ok(row.req_tseq)
      assert.ok(!row.native)			//Simulate query from downstream
      _done()
    })
    busA.register('pa', (msg) => {		//log.debug("A msg:", msg, "T:", msg.to, "F:", msg.from)
      interTest.m0 = msg			//Save original route message
      assert.equal(msg.target, 'route')
      assert.equal(msg.action, 'draft')
      assert.deepStrictEqual(msg.to, {cid:cidu, agent:agent0, host, port:port0})
      let obj = msg.object			//;log.debug("A obj:", obj, "F:", obj.find)
      assert.equal(obj.find.cid, cidd)
      assert.equal(obj.find.agent, agent2)
      assert.equal(obj.step, 0)
      assert.equal(obj.tally.length, 36)
      _done()
    })
  })

  it("Check view mychips.routes_v_paths", function(done) {
    let sql = `select json_agg(s) as json from (
          select edges,pat,inp_cid,inp_agent,circuit from mychips.routes_v_paths order by path) s;`
    queryJson('routes_v_paths', dbA, sql, done)
  })

  it("Agent transmits query, confirms change to pend (draft -> pend)", function(done) {
//log.debug("MSG:", interTest.m0)
    let logic = {context: ['draft'], update: {status: 'pend'}}
      , {to, from, object} = interTest.m0
      , msg = {to:from, from:to, object}
      , sql = Format(`select mychips.route_process(%L,%L) as state;`, msg, logic)
    interTest.m1 = msg
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res.rows[0])
      let row = getRow(res, 0)				//;log.debug("row:", row)
      assert.equal(row.state, 'pend')
      done()
    })
  })

  it("Save pend route record for later testing", function(done) {
    dbA.query(save('pend'), (e) => {if (e) done(e); done()})
  })

  it("Agent receives message of successful route (pend -> good)", function(done) {
    let logic = {context: ['pend'], update: {status: 'good'}}
      , msg = interTest.m1
      , sql0 = `update mychips.routes set min = 4, max = 9, margin = 0.001, reward = 0.015;`
      , sql1 = Format(`select mychips.route_process(%L,%L) as state;`, msg, logic)
      , dc = 2, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql0 + sql1)
    dbA.query(sql0 + sql1, null, (e, res) => {if (e) done(e)
      assert.equal(res.length, 2)
      let row = res[1].rows[0]			//;log.debug('r:', row)
      assert.equal(row.state, 'good')
      _done()
    })
    busA.register('pa', (msg) => {		//log.debug("A msg:", msg, "T:", msg.to, "F:", msg.from)
      assert.equal(msg.target, 'route')
      assert.equal(msg.action, 'good')
      assert.deepStrictEqual(msg.from, {cid:cid3, agent:agent1, host, port:port1})
      assert.deepStrictEqual(msg.to,   {cid:cidd, agent:agent2, host, port:port2})
      let obj = msg.object			//;log.debug("A obj:", obj, "L:", obj.lading)
      assert.deepStrictEqual(obj.lading, {min:4,max:5,margin:0.003994,reward:0.015000})
      assert.equal(obj.tally.length, 36)
      _done()
    })
  })

  it("Restore original pend route record", function(done) {
    dbA.query(rest('pend'), (e) => {if (e) done(e); done()})
  })

  it("Agent receives message of successful local/native route (pend -> good)", function(done) {
    let logic = {context: ['pend'], update: {status: 'good'}}
      , msg = interTest.m1
      , sql0 = `update mychips.routes set req_tseq = null;`
      , sql1 = Format(`select mychips.route_process(%L,%L) as state;`, msg, logic)
      , dc = 2, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql0 + sql1)
    dbA.query(sql0 + sql1, null, (e, res) => {if (e) done(e)
      assert.equal(res.length, 2)
      let row = res[1].rows[0]			//;log.debug('r:', row)
      assert.equal(row.state, 'good')
      _done()
    })
    busU.register('pu', (msg) => {		//;log.debug("U msg:", msg)
      assert.equal(msg.target, 'route')
      assert.equal(msg.action, 'good')
      let obj = msg.object			//;log.debug("U obj:", obj, "F:", obj.find)
      assert.deepStrictEqual(obj.find, {cid:cidd, agent:agent2})
      _done()
    })
  })

  it("Save good route record to D for lift testing", function(done) {
    dbA.query(save('goodD'), (e) => {if (e) done(e); done()})
  })

  it("Add two more possible external up-routes", function(done) {
     let units = 10, stat = 'open', sig = 'Valid'
       , cidA = 'cid_A', cidB = 'cid_B'
       , aCert = {chad:{cid:cidA, agent:agent0, host, port:port0}}
       , bCert = {chad:{cid:cidB, agent:agent0, host, port:port0}}
       , sql = Format(`with
       t0 as (select * from mychips.tallies where tally_ent = %L and tally_type = 'stock'),
       t2 as (select * from mychips.tallies where tally_ent = %L and tally_type = 'stock')
     insert into mychips.tallies
      (tally_ent, tally_type, contract, hold_cert, part_cert, hold_sig, part_sig, status)
      select t0.tally_ent, t0.tally_type, t0.contract, t0.hold_cert, %L, t0.hold_sig, %L, %L from t0
     union
      select t2.tally_ent, t2.tally_type, t2.contract, t2.hold_cert, %L, t2.hold_sig, %L, %L from t2
     returning *`, user0, user2, aCert, sig, stat, bCert, sig, stat)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res)
      let row = getRow(res, 0, 2)		//;log.debug("A row:", row)
//      assert.equal(row.part_cid, cidB)
      done()
    })
  })

  it("Find the tally ID info we need for next tests", function(done) {
     let sql = Format(`select * from mychips.tallies_v where hold_cid = %L and part_cid = %L;`, cid3, cidd)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("A row:", row)
      assert.equal(row.tally_ent, user3)
      interTest.t0 = row			//Save tally info
      done()
    })
  })

  it("Agent receives query for local user", function(done) {
    let step = 2
      , tally = interTest.t0.tally_uuid
      , msg = {target: 'route', action: 'query',
          to: {cid:cid3, agent:agent1},
          from: {cid:cidd, agent:agent2},
          object: {step, tally,
            find: {cid:cid1, agent:agent1}
          }
        }
      , dc = 2, _done = () => {if (!--dc) done()}
      , sql = Format(`select mychips.route_process(%L,%L) as state;`, msg, queryLogic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("A row:", row)
        , state = row.state			//;log.debug("A state:", state)
      assert.equal(state.action, 'good')	//;log.debug("A lading:", state.lading)
      assert.equal(state.forward, 1)
      assert.deepStrictEqual(state.lading, {"max":9,"min":7,"margin":0.001999,"reward":0.02})
      _done()
    })
    busA.register('pa', (msg) => {		//log.debug("A msg:", msg, "T:", msg.to, "F:", msg.from)
      assert.equal(msg.target, 'route')
      assert.equal(msg.action, 'draft')
      assert.deepStrictEqual(msg.from, {cid:cid2, agent:agent1, host, port:port1})
      assert.deepStrictEqual(msg.to,   {cid:cidb, agent:agent0, host, port:port0})
      let obj = msg.object			//;log.debug("A obj:", obj, "L:", obj.lading)
      assert.equal(obj.step, step)
      assert.equal(obj.tally.length, 36)
      _done()
    })
  })

  it("Should produce one more draft route record", function(done) {
    queryJson('routes_v1', dbA, routeSql, done)
  })

  it("Agent receives query for tally-connected foreign user", function(done) {
    let step = 7
      , tally = interTest.t0.tally_uuid
      , msg = {target: 'route', action: 'query',
          to: {cid:cid3, agent:agent1},
          from: {cid:cidd, agent:agent2},
          object: {step, tally,
            find: {cid:cidu, agent:agent0}
          }
        }
      , dc = 3, _done = () => {if (!--dc) done()}
      , sql = Format(`select mychips.route_process(%L,%L) as state;`, msg, queryLogic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("A row:", row)
          , state = row.state			//;log.debug("A state:", state)
      assert.equal(state.action, 'good')	//;log.debug("A lading:", state.lading)
      assert.equal(state.forward, 2)		//new queries sent along
      assert.deepStrictEqual(state.lading, {"max":7,"min":5,"margin":0.002997,"reward":0.02})
      _done()
    })
    busA.register('pa', (msg) => {		//log.debug("A msg:", msg, "T:", msg.to, "F:", msg.from)
      assert.equal(msg.target, 'route')
      assert.equal(msg.action, 'draft')

      if (msg.from.cid == cid2) {		//Should get called twice
        assert.deepStrictEqual(msg.to,   {cid:cidb, agent:agent0, host, port:port0})
      } else {
        assert.deepStrictEqual(msg.from, {cid:cid0, agent:agent1, host, port:port1})
        assert.deepStrictEqual(msg.to,   {cid:cida, agent:agent0, host, port:port0})
      }
      let obj = msg.object			//;log.debug("A obj:", obj, "L:", obj.lading)
      assert.equal(obj.step, step)
      assert.equal(obj.tally.length, 36)
      _done()
    })
  })

  it("Should produce three more draft route records", function(done) {
    queryJson('routes_v2', dbA, routeSql, done)
  })

  it("Agent receives query for unknown but queriable user", function(done) {
    let step = 2
      , tally = interTest.t0.tally_uuid
      , msg = {target: 'route', action: 'query',
          to: {cid:cid3, agent:agent1},
          from: {cid:cidd, agent:agent2},
          object: {step, tally,
            find: {cid:cidx, agent:agent0}
          }
        }
      , dc = 4, _done = () => {if (!--dc) done()}
      , sql = Format(`select mychips.route_process(%L,%L) as state;`, msg, queryLogic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("A row:", row)
          , state = row.state			//;log.debug("A state:", state)
      assert.equal(state.action, 'relay')	//;log.debug("A lading:", state.lading)
      assert.equal(state.forward, 3)
      assert.ok(!state.lading)
      _done()
    })
    busA.register('pa', (msg) => {		//log.debug("A msg:", msg, "T:", msg.to, "F:", msg.from)
      assert.equal(msg.target, 'route')
      assert.equal(msg.action, 'draft')

      if (msg.to.cid == cida) {		//Should get called three times
        assert.deepStrictEqual(msg.from, {cid:cid0, agent:agent1, host, port:port1})
      } else if (msg.to.cid == cidb) {
        assert.deepStrictEqual(msg.from, {cid:cid2, agent:agent1, host, port:port1})
      } else {
        assert.deepStrictEqual(msg.to,   {cid:cidu, agent:agent0, host, port:port0})
        assert.deepStrictEqual(msg.from, {cid:cid0, agent:agent1, host, port:port1})
      }
      let obj = msg.object			//;log.debug("A obj:", obj, "L:", obj.lading)
      assert.equal(obj.step, step)
      assert.equal(obj.tally.length, 36)
      _done()
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

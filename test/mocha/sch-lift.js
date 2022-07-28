//Test lift schema at a basic level; run after sch-route
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// Agent <-> DB <-> Agent
//TODO:
//- Test remaining state transitions needed for referee/crypto-signing:
//-   pend -> pend.check	pend.check -> pend
//-   seek.check -> seek
//-   seek.call -> seek
//-   seek.call -> call
//-   call -> call.call		call.call -> call
//- 
const { dbConf, testLog, Format, Bus, assert, getRow, mkUuid, dbClient, queryJson } = require('./common')
var log = testLog(__filename)
const { host, user0, port0, port1, port2, agent0, agent1, agent2 } = require('./def-users')
const { cidu, cidd, cidN } = require('./def-path')
var cid0 = cidN(0), cid2 = cidN(2), cid3 = cidN(3), cidb = cidN('B'), cidx = cidN('X')
var agentListen = 'ma_' + agent1		//And his agent process
var {save, rest} = require('./def-route')
var interTest = {}			//Pass values from one test to another

describe("Test lift state transitions", function() {
  var busA = new Bus('busA')
  var dbA

  before('Agent connection to database', function(done) {
    dbA = new dbClient(new dbConf(log,agentListen), (chan, data) => {
      log.trace("Notify from A channel:", chan, "data:", data)
      busA.notify(JSON.parse(data))
    }, ()=>{log.info("Test DB agent connection established"); done()})
  })

  it("Restore good route record to D from sch-route test", function(done) {
    dbA.query(rest('goodD'), (e) => {if (e) done(e); done()})
  })

  it("Delete existing lifts/chits, set simulated lading", function(done) {
    let sql = `delete from mychips.chits where chit_type = 'lift';
               delete from mychips.lifts;
               update mychips.tallies set clutch = 0.04;
               update mychips.tallies set target = 2 where tally_type = 'stock' and net_pc != 0;
               update mychips.tallies set target = 5 where tally_type = 'foil';`
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {done(e)})
  })

it("Configure existing good route in DB", function(done) {
    let min = 4
      , smallest = 2
      , sql = `update mychips.routes set min = ${min} where status = 'good' 
      returning *, base.parmset('lifts','minimum',${smallest}) as smallest;`
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("Q row:", row)
      interTest.r0 = row			//Save original route record
      assert.equal(row.min, min)
      assert.equal(row.via_ent, user0)
      assert.equal(row.dst_cid, cidd)
      assert.equal(row.dst_agent, agent2)
      assert.equal(row.smallest, smallest)
      done()
    })
  })

  it("Query resulting path/route", function(done) {
    let sql = `select bot_cid,top_cid,dst_cid,status,path,path_min,route_min,min
      from mychips.routes_v_paths where segment and status = 'good'`
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.bot_cid, cid3)
      assert.equal(row.top_cid, cid0)
      assert.equal(row.dst_cid, cidd)
      assert.equal(row.min, interTest.r0.min)	//As set in previous test
      done()
    })
  })

  it("Create new lift request (<start> -> draft.init)", function(done) {
    let sql = `select mychips.lift_dist();`
      , dc = 2, _done = () => {if (!--dc) done()}	//_done's to be done
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("Q res:", res.rows[0])
      let row = getRow(res, 0)
      assert.equal(row.lift_dist, 1)
      _done()
    })
    busA.register('pa', (msg) => {		//log.debug("A msg:", msg, 'T:', msg.to, 'F:', msg.from)
      interTest.init = msg			//Save initialization message for later
      assert.equal(msg.target, 'lift')
      assert.equal(msg.action, 'init')
      assert.equal(msg.sequence, 0)
      assert.deepStrictEqual(msg.outc, {cid:cidu, agent:agent0, host, port:port0})
      assert.deepStrictEqual(msg.topc, {cid:cid0, agent:agent1, host, port:port1})
      let obj = msg.object			//;log.debug("A obj:", obj)
      assert.ok(!obj.org)
      assert.ok(!obj.ref)
      assert.ok(!obj.find)
      assert.equal(obj.lift.length, 36)		//;log.debug("A r0:", interTest.r0)
      assert.equal(obj.units, interTest.r0.min)		//lift amount
      let init = msg.init			//;log.debug("A init:", init)
      assert.ok(init.circuit)
      assert.equal(init.find.cid, cidd)
      assert.equal(init.find.agent, agent2)
      assert.equal(init.org.agent, agent1)
      assert.equal(init.org.host, host)
      assert.equal(init.org.port, port1)
      assert.equal(init.ref.agent, agent1)
      assert.equal(init.ref.host, host)
      assert.equal(init.ref.port, port1)
      _done()
    })
  })

  it("Agent gets init action (draft.init -> init.seek)", function(done) {
    let logic = {context: ['draft.init'], update: null}
      , {action, object, init, sequence} = interTest.init
      , {ref, org, find, circuit} = init
      , lift_uuid = mkUuid(org.plan.cid, org.plan.agent, 'lift')
      , msg = {sequence, object}
    org.plan.pay = !circuit			//Payment or clearing lift
    org.plan = Buffer.from(JSON.stringify(org.plan)).toString('base64url')	//Fake encryption
    logic.update = {status: 'init', request: 'seek', lift_uuid, referee:ref, origin:org, find}
    let sql = Format(`select mychips.lift_process(%L,%L) as state;`, msg, logic)
      , dc = 2, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("Q res:", res.rows[0])
      let row = getRow(res, 0)
      assert.equal(row.state, 'init.seek')
      _done()
    })
    busA.register('pa', (msg) => {		//log.debug("A msg:", msg, 'OC:', msg.outc, 'Tc:', msg.topc)
      interTest.seek = msg
      assert.equal(msg.target, 'lift')
      assert.equal(msg.action, 'seek')
      assert.deepStrictEqual(msg.outc, {cid:cidu, agent:agent0, host, port:port0})
      assert.deepStrictEqual(msg.topc, {cid:cid0, agent:agent1, host, port:port1})
      assert.ok(!msg.init)
      let obj = msg.object			//;log.debug("A obj:", obj)
      assert.deepStrictEqual(obj.org, org)
      assert.deepStrictEqual(obj.ref, ref)
      assert.deepStrictEqual(obj.find, find)
      assert.equal(obj.lift, lift_uuid)
      _done()
    })
  })

  it("Agent gets seek action (init.seek -> seek)", function(done) {
    let logic = {context: ['init.seek'], update: {status: 'seek'}}
      , msg = interTest.seek		//;log.debug("msg:", interTest.seek, "O:", interTest.seek.object)
      , sql = Format(`select mychips.lift_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("Q res:", res.rows[0])
      let row = getRow(res, 0)
      assert.equal(row.state, 'seek')
      done()
    })
  })

  it("Check created lift tallies/chits", function(done) {
    let {lift, sequence} = interTest.seek
      , sql = `select json_agg(s) as json from (select tally_ent, tally_seq,tally_type,
               net,net_c,net_p,net_pc,chits,chits_p
               from mychips.tallies_v where chits > 0 order by 1,2) s;`
    queryJson('lift_chits', dbA, sql, done, 1)
  })

  it("Agent informs DB of timeout (seek -> seek.check)", function(done) {
    let logic = {context: ['seek'], update: {request: 'check'}}
      , msg = interTest.seek		//;log.debug("msg:", interTest.seek, "O:", interTest.seek.object)
      , sql = Format(`select mychips.lift_process(%L,%L) as state;`, msg, logic)
      , dc = 2, _done = () => {if (!--dc) done()}	//_done's to be done
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("Q res:", res.rows[0])
      let row = getRow(res, 0)
      assert.equal(row.state, 'seek.check')
      _done()
    })
    busA.register('pa', (msg) => {		//log.debug("A msg:", msg)
//      interTest.check = msg
      assert.equal(msg.target, 'lift')
      assert.equal(msg.action, 'check')
      _done()
    })
  })

  it("Agent seeks signature from partner,originator,referee (init.seek -> seek)", function(done) {
    let logic = {context: ['seek.check'], update: {status: 'seek'}}
      , msg = interTest.seek		//;log.debug("msg:", interTest.check, "O:", interTest.check.object)
      , sql = Format(`select mychips.lift_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("Q res:", res.rows[0])
      let row = getRow(res, 0)
      assert.equal(row.state, 'seek')
      done()
    })
  })

  it("Restore good route record to X from sch-route test", function(done) {
    dbA.query(rest('goodX'), (e) => {done(e)})
  })

  it("Agent receives promise for known foreign destination (<start> -> draft.relay)", function(done) {
    let logic = {query: true}			//;log.debug("init:", interTest.init)
      , tally = interTest.init.bott		//;log.debug("bottom:", tally)	//tally: 3->D
      , find = {cid:cidx, agent:agent0}
      , lift = mkUuid(cidd, agent2, 'lift')
      , {org, ref, date, life, units} = interTest.seek.object
      , object = {org, ref, date, find, life, lift, units}
      , msg = {tally, object}
      , sql = Format(`select mychips.lift_process(%L,%L) as state;`, msg, logic)
      , dc = 2, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql)
    interTest.relay = msg
    dbA.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("Q res:", res.rows[0])
      let row = getRow(res, 0)
      assert.equal(row.state, 'draft.relay')
      _done()
    })
    busA.register('pa', (msg) => {		//log.debug("A msg:", msg, 'IC:', msg.inpc, 'Tc:', msg.botc)
//      interTest.check = msg
      assert.equal(msg.target, 'lift')
      assert.equal(msg.action, 'relay')
      assert.deepStrictEqual(msg.outc, {cid:cidb, agent:agent0, host, port:port0})
      assert.deepStrictEqual(msg.topc, {cid:cid2, agent:agent1, host, port:port1})
      _done()
    })
  })

  it("Agent receives promise for connected foreign destination (<start> -> draft.relay)", function(done) {
    let logic = {query: true}			//;log.debug("relay:", interTest.relay)
      , find = {cid:cidu, agent:agent0}
      , msg = interTest.relay			//From previous test
      , lift = mkUuid(cidd, agent2, 'lift')
      , units = 1
    msg.object = Object.assign(msg.object, {find, lift, units})
    let sql = Format(`select mychips.lift_process(%L,%L) as state;`, msg, logic)
      , dc = 2, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("Q res:", res.rows[0])
      let row = getRow(res, 0)
      assert.equal(row.state, 'draft.relay')
      _done()
    })
    busA.register('pa', (msg) => {		//log.debug("A msg:", msg, 'IC:', msg.inpc, 'Tc:', msg.botc)
      interTest.forcon = msg
      assert.equal(msg.target, 'lift')
      assert.equal(msg.action, 'relay')
      assert.deepStrictEqual(msg.outc, {cid:cidu, agent:agent0, host, port:port0})
      assert.deepStrictEqual(msg.topc, {cid:cid0, agent:agent1, host, port:port1})
      _done()
    })
  })

  it("Agent gets relay action (draft.relay -> pend)", function(done) {
    let logic = {context: ['draft.relay'], update: {status: 'pend'}}
      , msg = interTest.forcon		//;log.debug("msg:", interTest.seek, "O:", interTest.seek.object)
      , sql = Format(`select mychips.lift_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("Q res:", res.rows[0])
      let row = getRow(res, 0)
      assert.equal(row.state, 'pend')
      done()
    })
  })

  it("Agent receives promise for local user (<start> -> draft.found)", function(done) {
    let logic = {query: true}
      , find = {cid:cid3, agent:agent1}
      , msg = interTest.relay			//From previous test
      , lift = mkUuid(cidd, agent2, 'lift')
      , units = 3
    msg.object = Object.assign(msg.object, {find, lift, units})
    let sql = Format(`select mychips.lift_process(%L,%L) as state;`, msg, logic)
      , dc = 2, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("Q res:", res.rows[0])
      let row = getRow(res, 0)
      assert.equal(row.state, 'draft.found')
      _done()
    })
    busA.register('pa', (msg) => {		//log.debug("A msg:", msg, 'IC:', msg.inpc, 'Tc:', msg.botc)
      interTest.forloc = msg
      assert.equal(msg.target, 'lift')
      assert.equal(msg.action, 'found')
      assert.deepStrictEqual(msg.inpc, {cid:cidd, agent:agent2, host, port:port2})
      assert.deepStrictEqual(msg.botc, {cid:cid3, agent:agent1, host, port:port1})
      _done()
    })
  })

  it("Agent gets found action (draft.found -> pend)", function(done) {
    let logic = {context: ['draft.found'], update: {status: 'pend'}}
      , msg = interTest.forloc		//;log.debug("msg:", interTest.seek, "O:", interTest.seek.object)
      , sql = Format(`select mychips.lift_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("Q res:", res.rows[0])
      let row = getRow(res, 0)
      assert.equal(row.state, 'pend')
      done()
    })
  })

  it("Agent receives terminus confirmation (seek -> seek.call)", function(done) {
    let logic = {context: ['seek'], update: {request: 'call'}}	//;log.debug("Seek:", interTest.seek)
      , seek = interTest.seek				//;log.debug("O:", seek.object)
      , sobj = seek.object				//;log.debug("Org:", sobj.org, "Find:", sobj.find, "Ref:", sobj.ref)
      , lift = sobj.lift
      , tally = seek.bott				//;log.debug("Base:", tally)
      , {org, ref, date, life, units, find} = sobj
      , object = {org, ref, date, find, life, lift, units}
      , msg = {tally, object}
      , sql = Format(`select mychips.lift_process(%L,%L) as state;`, msg, logic)
      , dc = 2, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql)
    interTest.relay = msg
    dbA.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("Q res:", res.rows[0])
      let row = getRow(res, 0)
      assert.equal(row.state, 'seek.call')
      _done()
    })
    busA.register('pa', (msg) => {		//log.debug("A msg:", msg, 'IC:', msg.inpc, 'Tc:', msg.botc)
      assert.equal(msg.target, 'lift')
      assert.equal(msg.action, 'call')
      _done()
    })
  })

/* */
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{		//Let it flush out before closing
      dbA.disconnect()
      done()
      }, 200)
  })
})

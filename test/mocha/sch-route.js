//Test route schema at a basic level; run after sch-paths
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// User <-> DB <-> Agent
//TODO:
//- 
const Fs = require('fs')
const { dbConf, Log, Format, Bus, assert, getRow, mkUuid, dbClient } = require('./common')
var log = Log('testSchRoute')
const { host, user0, user3, port0, port1, port2, agent0, agent1, agent2 } = require('./def-users')
const { cidu, cidd, cidN } = require('./def-path')
var cid1 = cidN(1), cid2 = cidN(2), cid3 = cidN(3)
var userListen = 'mu_' + user3
var agentListen = 'ma_' + agent1		//And his agent process
var {save, rest} = require('./def-route')
var queryLogic = {context: ['null','none','pend.X','good.X'], query: true}
var interTest = {}			//Pass values from one test to another

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

  it("Create new external request draft route (<start> -> draft)", function(done) {
    let sql = `with
          inp as (select tally_ent as ent, tally_seq as seq from mychips.tallies where tally_type = 'stock' and part_ent isnull),
          dst as (select tally_ent as ent, tally_seq as seq, part_cid as cid, part_agent as agent from mychips.tallies where tally_type = 'foil' and part_ent isnull)
        insert into mychips.routes_v (via_ent, via_tseq, dst_cid, dst_agent, req_ent, req_tseq)
          select inp.ent, inp.seq, dst.cid, dst.agent, dst.ent, dst.seq from inp,dst returning *;`
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
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
    busA.register('pa', (msg) => {		//;log.debug("A msg:", msg, "T:", msg.to, "F:", msg.from)
      interTest.m0 = msg			//Save original route message
      assert.equal(msg.target, 'route')
      assert.equal(msg.action, 'draft')
      assert.deepStrictEqual(msg.to, {cid:cidu, agent:agent0, host, port:port0})
      let obj = msg.object			//;log.debug("A obj:", obj, "F:", obj.find)
      assert.equal(obj.find.cid, cidd)
      assert.equal(obj.find.agent, agent2)
      assert.equal(obj.step, 0)
      assert.equal(obj.tally.length, 36)
      busA.register('pa')
      _done()
    })
  })

  it("Check view mychips.routes_v_paths", function(done) {
    let expFile = 'routes_v_paths.json'
      , sql = `select json_agg(s) as json from (
          select edges,pat,bot_cid,bot_agent,circuit from mychips.routes_v_paths order by path) s;`
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)				//;log.debug("row:", row)
//      Fs.writeFileSync(expFile+'.tmp', JSON.stringify(row.json,null,1))		//Save actual results
      Fs.readFile(expFile, (e, fData) => {if (e) done(e)
        let expObj = JSON.parse(fData)
        assert.deepStrictEqual(row.json, expObj)
        done()
      })
    })
  })

  it("Agent transmits query, confirms change to pend (draft -> pend)", function(done) {
//log.debug("MSG:", interTest.m0)
    let logic = {context: ['draft'], update: {status: 'pend'}}
      , { cid, agent } = interTest.m0.from
      , msg = {to: {cid, agent}, object: interTest.m0.object}
      , sql = Format(`select mychips.route_process(%L,%L) as state;`, msg, logic)
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
      , { cid, agent } = interTest.m0.from
      , msg = {to: {cid, agent}, object: interTest.m0.object}
      , sql0 = `update mychips.routes set min = 4, max = 9, margin = 0.001, reward = 0.015;`
      , sql1 = Format(`select mychips.route_process(%L,%L) as state;`, msg, logic)
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
//log.debug("Sql:", sql0 + sql1)
    dbA.query(sql0 + sql1, null, (e, res) => {if (e) done(e)
      assert.equal(res.length, 2)
      let row = res[1].rows[0]			//;log.debug('r:', row)
      assert.equal(row.state, 'good')
      _done()
    })
    busA.register('pa', (msg) => {		//;log.debug("A msg:", msg, "T:", msg.to, "F:", msg.from)
      assert.equal(msg.target, 'route')
      assert.equal(msg.action, 'good')
      assert.deepStrictEqual(msg.from, {cid:cid3, agent:agent1, host, port:port1})
      assert.deepStrictEqual(msg.to,   {cid:cidd, agent:agent2, host, port:port2})
      let obj = msg.object			//;log.debug("A obj:", obj, "L:", obj.lading)
      assert.deepStrictEqual(obj.lading, {min:4,max:5,margin:0.003994,reward:0.015000})
      assert.equal(obj.tally.length, 36)
      busA.register('pa')
      _done()
    })
  })

  it("Restore original pend route record", function(done) {
    dbA.query(rest('pend'), (e) => {if (e) done(e); done()})
  })

  it("Agent receives message of successful local/native route (pend -> good)", function(done) {
    let logic = {context: ['pend'], update: {status: 'good'}}
      , { cid, agent } = interTest.m0.from
      , msg = {to: {cid, agent}, object: interTest.m0.object}
      , sql0 = `update mychips.routes set req_tseq = null;`
      , sql1 = Format(`select mychips.route_process(%L,%L) as state;`, msg, logic)
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
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
      busU.register('pu')
      _done()
    })
  })

  it("Save good route record for later testing", function(done) {
    dbA.query(save('good'), (e) => {if (e) done(e); done()})
  })

  it("Restore original pend route record", function(done) {
    dbA.query(rest('pend'), (e) => {if (e) done(e); done()})
  })

  it("Agent receives message of failed route (pend -> none)", function(done) {
    let logic = {context: ['pend'], update: {status: 'none'}}
      , { cid, agent } = interTest.m0.from
      , msg = {to: {cid, agent}, object: interTest.m0.object}
      , sql = Format(`select mychips.route_process(%L,%L) as state;`, msg, logic)
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)
      assert.equal(row.state, 'none')
      _done()
    })
    busA.register('pa', (msg) => {		//;log.debug("A msg:", msg, "T:", msg.to, "F:", msg.from)
      assert.equal(msg.target, 'route')
      assert.equal(msg.action, 'none')
      busA.register('pa')
      _done()
    })
  })

  it("Restore good route record", function(done) {
    dbA.query(rest('good'), (e) => {if (e) done(e); done()})
  })

  it("Find the tally ID info we need for next test", function(done) {
     let sql = Format(`select * from mychips.tallies_v where hold_cid = %L and part_cid = %L;`, cid3, cidd)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("A row:", row)
      assert.equal(row.tally_ent, user3)
      interTest.t0 = row			//Save tally info
      done()
    })
  })
/*
  it("Agent receives query for local user (none -> pend)", function(done) {
    let step = 2
      , tally = interTest.t0.tally_uuid
      , msg = {target: 'route', action: 'query',
          to: {cid:cid3, agent:agent1},
          from: {cid:cidd, agent:agent2},
          object: {step, tally,
            find: {cid:cid1, agent:agent1}
          }
        }
      , sql = Format(`select mychips.route_process(%L,%L) as state;`, msg, queryLogic)
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			;log.debug("A row:", row)
//      assert.equal(row.state, 'none')
      _done()
    })
    busA.register('pa', (msg) => {		;log.debug("A msg:", msg, "T:", msg.to, "F:", msg.from)
      assert.equal(msg.target, 'route')
//      assert.equal(msg.action, 'none')
      busA.register('pa')
      _done()
    })
  })

//  it("Clear route table", function(done) {
//    dbA.query('delete from mychips.routes', null, (e, res) => {done(e)})
//  })

/*
*/
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{		//Let it flush out before closing
      dbU.disconnect()
      dbA.disconnect()
      done()
      }, 200)
  })
})

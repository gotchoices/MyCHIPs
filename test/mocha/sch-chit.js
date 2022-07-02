//Test chit schema at a basic level; run after sch-tally
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// User <-> DB <-> Agent
//TODO:
//- 
const { dbConf, testLog, Format, Bus, assert, getRow, mkUuid, dbClient } = require('./common')
var log = testLog(__filename)
const { host, cid0, cid1, user0, user1, agent0, agent1, aKey0, aKey1 } = require('./def-users')
var userListen = 'mu_' + user0
var agentListen = 'ma_' + agent0		//And his agent process
var contract = {domain:"mychips.org", name:"standard", version:0.99}
var defTally = require('./def-tally')
var {stateField, uSql, save, rest} = require('./def-chit')
var interTest = {}			//Pass values from one test to another

describe("Test chit state transitions", function() {
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

  it("Restore open tallies", function(done) {
    dbA.query(defTally.rest('open'), (e) => {if (e) done(e); else done()})
  })

  it("Initialize DB", function(done) {
    let sql = `begin;
        delete from mychips.chits;
        update mychips.tallies set _last_chit = 0 where tally_ent = %L and status = 'open' returning tally_ent, tally_seq; commit`
    dbA.query(Format(sql, user0), (e, res) => {if (e) done(e)
      assert.equal(res[2].rowCount, 1)
      let row = res[2].rows[0]			//;log.debug('row O:', row)
      assert.equal(row.tally_ent, user0)
      interTest.tally = row			//Save base tally for later tests
      done()
    })
  })

  it("Build draft invoice chit record (<start> -> A.draft.pend)", function(done) {
    let uuid = mkUuid(cid0, agent0, 'chit')
      , ent = interTest.tally.tally_ent
      , seq = interTest.tally.tally_seq
      , value = 123400
      , ref = {a: 'A test'}
      , request = 'pend'
      , dc = 2, _done = () => {if (!--dc) done()}
      , sql = Format(`insert into mychips.chits_v (chit_ent, chit_seq, chit_uuid, chit_type, units, reference, request)
          values (%L, %s, %L, 'tran', %s, %L, %L) returning *`, ent, seq, uuid, value, ref, request)
//log.debug("Sql:", sql)
    dbU.query(sql, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("Row:", row)
      assert.equal(row.chit_ent, ent)
      assert.equal(row.chit_seq, seq)
      assert.equal(row.units, value)
      assert.equal(row.status,'draft')
      assert.equal(row.request,'pend')
      assert.equal(row.net_p, value)
      assert.equal(row.net_g, 0)
      assert.equal(row.tally_type, 'stock')
      assert.equal(row.action, false)
      assert.equal(row.state,'A.draft.pend')
      _done()
    })
    busA.register('pa', (msg) => {		//log.debug('BusA:', msg, msg.to, msg.from)
      assert.equal(msg.target, 'chit')
      assert.equal(msg.action, 'pend')
      assert.equal(msg.to.cid, cid1)
      assert.equal(msg.to.agent, agent1)
      let obj = msg.object			//;log.debug("A obj:", obj)
      assert.deepStrictEqual(obj.ref, ref)
      assert.equal(obj.type, 'tran')
      assert.equal(obj.by, 'foil')
      assert.equal(obj.units, value)
      assert.equal(obj.uuid, uuid)
      assert.ok(!obj.signed)
      interTest.chit = obj			//Save original chit object
      interTest.from = msg.from			//And info about our user
      _done()
    })
  })

  it("Build generic transmit messages for later tests", function() {
    let { cid, agent } = interTest.from		//Return message to sender
      , msg = {to: {cid, agent}, object: interTest.chit}
    interTest.pSql = (logic, uuid) => {
      if (uuid) {msg.object.uuid = uuid}
      return Format(`select mychips.chit_process(%L,%L) as state;`, msg, logic)
    }
  })

  it("Agent transmits, confirms change to pend (A.draft.pend -> A.pend)", function(done) {
    let sql = interTest.pSql({context: ['A.draft.pend'], update: {status: 'pend'}})
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.state, 'A.pend')
      done()
    })
  })

  it("Save A.pend chit record for later testing", function(done) {
    dbA.query(save('apend'), (e) => {if (e) done(e); done()})
  })

  it("Peer rejects invoice chit (A.pend -> A.void)", function(done) {
    let sql = interTest.pSql({context: ['A.pend'], update: {status: 'void'}})
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)
      let row = getRow(res, 0)				//;log.debug("row:", row)
      assert.equal(row.state, 'A.void')
      done()
    })
  })

  it("User requests modified invoice chit (A.void -> A.draft.pend)", function(done) {
    let value = 12340
      , sql = uSql(`request = 'pend', units = ` + value, user0, interTest.chit.uuid)
      , dc = 2, _done = () => {if (!--dc) done()}	//2 _done's to be done
//log.debug("Sql:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.state, 'A.draft.pend')
      assert.equal(row.action, false)
      _done()
    })
    busA.register('pa', (msg) => {		//;log.debug("A msg:", msg)
      assert.equal(msg.target, 'chit')
      assert.equal(msg.action, 'pend')
      let obj = msg.object			//;log.debug("A obj:", obj)
      assert.equal(obj.uuid, interTest.chit.uuid)
      assert.equal(obj.units, value)
      _done()
    })
  })

  it("Restore A.pend chit", function(done) {
    dbA.query(rest('apend'), (e) => {if (e) done(e); else done()})
  })

  it("Peer accepts invoice chit (A.pend -> A.good)", function(done) {
    let cmt = 'A modified comment'
      , object = Object.assign({}, interTest.chit, {for:cmt, signed: cid1 + ' signature'})
      , logic = {context: ['null','A.void','A.draft','A.pend'], upsert: {status: 'good'}}
      , { cid, agent } = interTest.from
      , msg = {to: {cid, agent}, object}
      , sql = Format(`select mychips.chit_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)
      let row = getRow(res, 0)				//;log.debug("row:", row)
      assert.equal(row.state, 'A.good')
      done()
    })
  })

  it("Agent receives good, signed chit (<start> -> A.good)", function(done) {
    let uuid = mkUuid(cid1, agent1, 'chit')
      , units = 987654
      , object = Object.assign({}, interTest.chit, {uuid, units, signed: cid1 + ' signature'})
      , logic = {context: ['null','A.void','A.draft','A.pend'], upsert: {status: 'good'}}
      , { cid, agent } = interTest.from
      , msg = {to: {cid, agent}, object}
      , sql = Format(`select mychips.chit_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("A row:", row)
      assert.equal(row.state, 'A.good')
      done()
    })
  })

  it("Build committed chit record (<start> -> L.pend.good)", function(done) {
    let uuid = mkUuid(cid0, agent0, 'chit')
      , ent = interTest.tally.tally_ent
      , seq = interTest.tally.tally_seq
      , by = 'stock'			//Liability
      , value = 123456	
      , ref = {cmt: 'Uninvoiced transfer'}
      , request = 'good'
      , signature = cid0 + ' signature'
      , dc = 2, _done = () => {if (!--dc) done()}
      , sql = Format(`insert into mychips.chits_v (chit_ent, chit_seq, chit_uuid, chit_type, issuer, units, reference, request, signature)
          values (%L, %s, %L, 'tran', %L, %s, %L, %L, %L) returning *`, ent, seq, uuid, by, value, ref, request, signature)
//log.debug("Sql:", sql)
    dbU.query(sql, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("Row:", row)
      assert.equal(row.units, value)
      assert.equal(row.status,'pend')
      assert.equal(row.request,'good')
      assert.equal(row.state,'L.pend.good')
      assert.equal(row.net_p, -value)		//Stock issue accrues negative
      assert.equal(row.action, false)
      assert.equal(row.net_g, 0)
      _done()
    })
    busA.register('pa', (msg) => {		//log.debug('BusA:', msg, msg.to, msg.from)
      assert.equal(msg.target, 'chit')
      assert.equal(msg.action, 'good')
      assert.equal(msg.to.cid, cid1)
      assert.equal(msg.to.agent, agent1)
      let obj = msg.object			//;log.debug("A obj:", obj)
      assert.deepStrictEqual(obj.ref, ref)
      assert.equal(obj.by, by)
      assert.equal(obj.type, 'tran')
      assert.equal(obj.units, value)
      assert.equal(obj.uuid, uuid)
      assert.equal(obj.signed, signature)
      _done()
    })
  })

  it("Agent receives invoice chit (<start> -> A.good)", function(done) {
    let uuid = mkUuid(cid1, agent1, 'chit')
      , by = 'stock'
      , units = 87654
      , object = Object.assign({}, interTest.chit, {uuid, by, units})
      , logic = {context: ['null','L.void','L.pend'], upsert: {status: 'pend'}}
      , { cid, agent } = interTest.from
      , msg = {to: {cid, agent}, object}
      , sql = Format(`select mychips.chit_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.state, 'L.pend')
      interTest.chit = object			//Now dealing with this chit
      done()
    })
  })

  it("Save L.pend chit record for later testing", function(done) {
    dbA.query(save('lpend'), (e) => {if (e) done(e); done()})
  })

  it("User rejects invoice chit (L.pend -> L.pend.void)", function(done) {
    let sql = uSql(`request = 'void'`, user0, interTest.chit.uuid)
      , dc = 2, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.state, 'L.pend.void')
      assert.equal(row.action, false)
      _done()
    })
    busA.register('pa', (msg) => {
      assert.equal(msg.action, 'void')		//;log.debug("A obj:", msg.object)
      interTest.uuid = msg.object.uuid		//Redirect future tests to this latest chit
      _done()
    })
  })

  it("Agent transmits, confirms change to void (L.pend.void -> L.void)", function(done) {
    let sql = interTest.pSql({context: ['L.pend.void'], update: {status: 'void'}}, interTest.uuid)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.state, 'L.void')
      done()
    })
  })

  it("Agent receives revised good, signed chit (A.void -> A.good)", function(done) {
    let uuid = mkUuid(cid1, agent1, 'chit')
      , by = 'foil'
      , units = 32500
      , object = Object.assign({}, interTest.chit, {uuid, by, units, signed: cid1 + ' signature'})
      , logic = {context: ['null','A.void','A.draft','A.pend'], upsert: {status: 'good'}}
      , { cid, agent } = interTest.from
      , msg = {to: {cid, agent}, object}
      , sql = Format(`select mychips.chit_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.state, 'A.good')
      done()
    })
  })

  it("Restore L.pend chit", function(done) {
    dbA.query(rest('lpend'), (e) => {if (e) done(e); else done()})
  })

  it("User accepts invoice chit (L.pend -> L.pend.good)", function(done) {
    let sql = uSql(`request = 'good', signature = '` + cid0 + ` signature'`, user0, interTest.chit.uuid)
      , dc = 2, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.state, 'L.pend.good')
      assert.equal(row.action, false)
      _done()
    })
    busA.register('pa', (msg) => {
      assert.equal(msg.action, 'good')		//;log.debug("A obj:", msg.object)
      _done()
    })
  })

  it("Agent transmits, confirms change to good (L.pend.good -> L.good)", function(done) {
    let sql = interTest.pSql({context: ['L.pend.good'], update: {status: 'good'}}, interTest.uuid)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.state, 'L.good')
      done()
    })
  })

  it("Commit trading variable chit record (<start> -> User.pend.good)", function(done) {
    let uuid = mkUuid(cid0, agent0, 'chit')
      , ent = interTest.tally.tally_ent
      , seq = interTest.tally.tally_seq
      , ref = {
        target: '1234',
        bound:  '2345',
        reward: '0.12',
        clutch: '0.05',
        limit:  '3456',
        close: true
      }
      , by = 'stock'
      , request = 'good'
      , signature = cid0 + ' signature'
      , dc = 2, _done = () => {if (!--dc) done()}
      , sql = Format(`insert into mychips.chits_v (chit_ent, chit_seq, chit_uuid, chit_type, issuer, reference, request, signature)
          values (%L, %s, %L, 'set', %L, %L, %L, %L) returning *`, ent, seq, uuid, by, ref, request, signature)
//log.debug("Sql:", sql)
    dbU.query(sql, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("Row:", row)
      assert.ok(!row.units)			//Null for settings
      assert.equal(row.status,'pend')
      assert.equal(row.request,'good')
      assert.equal(row.state,'L.pend.good')
      assert.equal(row.action, false)
      interTest.ref = ref
      _done()
    })
    busA.register('pa', (msg) => {		//log.debug('BusA:', msg, msg.to, msg.from)
      assert.equal(msg.target, 'chit')
      assert.equal(msg.action, 'good')
      assert.equal(msg.to.cid, cid1)
      assert.equal(msg.to.agent, agent1)
      let obj = msg.object			//;log.debug("A obj:", JSON.stringify(obj))
      assert.deepStrictEqual(obj.ref, ref)
      assert.equal(obj.by, by)
      assert.equal(obj.type, 'set')
      assert.equal(obj.uuid, uuid)
      assert.equal(obj.signed, signature)

      interTest.from = msg.from			//For next test
      interTest.chit = obj
      _done()
    })
  })

  it("Agent transmits settings, confirms change to good (L.pend.good -> L.good)", function(done) {
    let msg = {to: interTest.from, object: interTest.chit}
      , logic = {context: ['L.pend.good'], update: {status: 'good'}}
      , sql = Format(`select mychips.chit_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.state, 'L.good')
      done()
    })
//    busA.register('pa', (msg) => {		log.debug('BusA:', msg, msg.to, msg.from)
//      assert.equal(msg.target, 'tally')		//Propagate close request to partner
//      assert.equal(msg.action, 'close')
//      _done()
//    })
  })

  it("Verify tally properties are changed", function(done) {
    let msg = {to: interTest.from, object: interTest.chit}
      , logic = {context: ['L.pend.good'], update: {status: 'good'}}
      , sql = Format(`select state,target,bound,reward,clutch,hold_sets from mychips.tallies_v where tally_uuid = %L;`, interTest.chit.tally)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.state, 'close')
      assert.equal(row.target, interTest.ref.target)
      assert.equal(row.bound, interTest.ref.bound)
      assert.equal(row.reward, interTest.ref.reward)
      assert.equal(row.clutch, interTest.ref.clutch)
      assert.equal(row.hold_sets.target, row.target)
      assert.equal(row.hold_sets.bound, row.bound)
      assert.equal(row.hold_sets.reward, row.reward)
      assert.equal(row.hold_sets.clutch, row.clutch)
      done()
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
})		//Peer to peer tallies

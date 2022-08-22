//Test tally schema at a basic level; run after impexp, testusers
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
var {stateField, uSql, save, rest} = require('./def-tally')
var interTest = {}			//Pass values from one test to another

describe("Test tally state transitions", function() {
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

  it("Initialize DB", function(done) {
    let sql = `begin;
        delete from mychips.tallies;
        update mychips.users set _last_tally = 0; commit`
    dbA.query(sql, (e) => {if (e) done(e); done()})
  })

  it("Build draft tally record (<start> -> draft)", function(done) {
    let comment = 'Sample tally'
      , uuid = mkUuid(cid0, agent0)
      , s = `insert into mychips.tallies_v (tally_ent, tally_uuid, contract, comment, part_cert)
	    	values(%L,%L,%L,%L,mychips.user_cert(%L)) returning *, ${stateField};`
      , sql = Format(s, user0, uuid, contract, comment, user1)
//log.debug("Sql:", sql)
    dbU.query(sql, (e, res) => {if (e) done(e)		//;log.debug("Res:", res)
      let tal = getRow(res, 0)
      assert.equal(tal.version, 1)
      assert.equal(tal.tally_seq, 1)
      assert.equal(tal.tally_uuid, uuid)
      assert.equal(tal.status,'draft')
      assert.equal(tal.state,'draft')
      done()
    })
  })

  it("Save draft tally record for later testing", function(done) {
    dbA.query(save('draft'), (e) => {if (e) done(e); done()})
  })

  it("User request to promote tally to offer (draft -> draft.offer)", function(done) {
    let sql = uSql(`request = 'offer', hold_sig = '${cid0 + ' signature'}'`, user0, 1)
      , dc = 2, _done = () => {if (!--dc) done()}	//2 _done's to be done
//log.debug("Sql:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res.rows[0])
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
      _done()
    })
  })

  it("Agent transmits, confirms change to offer (draft.offer -> H.offer)", function(done) {
    let logic = {context: ['draft.offer'], update: {status: 'offer'}}
      , { cid, agent } = interTest.from
      , msg = {to: {cid, agent}, object: interTest.object}
      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0])
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
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0])
      let row = getRow(res, 0)
      assert.equal(row.state, 'P.offer')
      done()
    })
  }

  it("Agent receives alternative draft (H.offer -> P.offer)", function(done) {peerProfferGo(done)})
  
  it("User request to promote tally to offer (P.offer -> P.offer.void)", function(done) {
    let sql = uSql(`request = 'void', hold_sig = null`, user0, 1)
      , dc = 2, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res.rows[0])
      let row = getRow(res, 0)
      assert.equal(row.state, 'P.offer.void')
      _done()
    })
    busA.register('pa', (msg) => {		//Listen for message to agent process
//log.debug("sign:", msg.object.sign)
      assert.equal(msg.target, 'tally')
      assert.equal(msg.action, 'void')
      _done()
    })
  })

  it("Agent transmits, confirms change to void (P.offer.void -> void)", function(done) {
    let logic = {context: ['P.offer.void'], update: {status: 'void'}}
      , { cid, agent } = interTest.from
      , msg = {to: {cid, agent}, object: interTest.object}
      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0])
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
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0])
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
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0])
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
      , dc = 2, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res.rows[0])
      let row = getRow(res, 0)
//log.debug("X:", row.request, row.status, row.hold_sig, row.part_sig)
      assert.equal(row.state, 'draft.offer')
      _done()
    })
    busA.register('pa', (msg) => {		//Listen for message to agent process
      assert.equal(msg.target, 'tally')
      assert.equal(msg.action, 'offer')
      _done()
    })
  })

  it("Restore P.offer tally", function(done) {
    dbA.query(rest('Poffer'), (e) => {if (e) done(e); done()})
  })

  it("User request to accept draft (P.offer -> B.offer.open)", function(done) {
    let sql = uSql(`request = 'open', hold_sig = '${cid0 + ' signature'}'`, user0, 1)	//Force chips cache to non-zero
      , dc = 2, _done = () => {if (!--dc) done()}
//log.debug("Sql M:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res.rows[0])
      let row = getRow(res, 0)
      assert.equal(row.state, 'B.offer.open')
      _done()
    })
    busA.register('pa', (msg) => {		//Listen for message to agent process
      assert.equal(msg.target, 'tally')
      assert.equal(msg.action, 'open')
      _done()
    })
  })

  it("Agent transmits, confirms change to open (B.offer.open -> open)", function(done) {
    let logic = {context: ['B.offer.open'], update: {status: 'open'}}
      , { cid, agent } = interTest.from
      , msg = {to: {cid, agent}, object: interTest.object}
      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0])
      let row = getRow(res, 0)
      assert.equal(row.state, 'open')
      done()
    })
  })

  it("Save open tally record for later chit testing", function(done) {
    dbA.query(save('open'), (e) => {if (e) done(e); else done()})
  })

//Closing procedure moved to setting chit protocol
//  it("User request to close tally (open -> open.close)", function(done) {
//    let sql = uSql(`request = 'close'`, user0, 1)
//      , dc = 2, _done = () => {if (!--dc) done()}
////log.debug("Sql M:", sql)
//    dbU.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res.rows[0])
//      let row = getRow(res, 0)
//      assert.equal(row.state, 'open.close')
//      _done()
//    })
//    busA.register('pa', (msg) => {		//Listen for message to agent process
//      assert.equal(msg.target, 'tally')
//      assert.equal(msg.action, 'close')
//      _done()
//    })
//  })
//
//  it("Agent transmits, confirms change to close (open.close -> close)", function(done) {
//    let logic = {context: ['open.close'], update: {status: 'close'}}
//      , { cid, agent } = interTest.from
//      , msg = {to: {cid, agent}, object: interTest.object}
//      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
////log.debug("Sql:", sql)
//    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0])
//      let row = getRow(res, 0)
//      assert.equal(row.state, 'close')
//      done()
//    })
//  })
//
//  it("Restore open tally", function(done) {
//    dbA.query(rest('open'), (e) => {if (e) done(e); else done()})
//  })
//  it("Peer requests tally close (open -> close)", function(done) {
//    let object = {uuid: interTest.object.uuid}		//Minimal object
//      , logic = {context: ['open'], update: {status: 'close'}}
//      , { cid, agent } = interTest.from
//      , msg = {to: {cid, agent}, object}
//      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
////log.debug("Sql:", sql)
//    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0])
//      let row = getRow(res, 0)
//      assert.equal(row.state, 'close')
//      done()
//    })
//  })

/* */
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{		//Let it flush out before closing
      dbU.disconnect()
      dbA.disconnect()
      done()
      }, 200)
  })
})		//Peer to peer tallies

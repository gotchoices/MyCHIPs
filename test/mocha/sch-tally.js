//Test tally schema at a basic level; run after impexp, testusers
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// User <-> DB <-> Agent
//TODO:
//- Should be monitoring busU also?
//- 
const { dbConf, Log, Format, Bus, assert, getRow, mkUuid } = require('../settings')
var log = Log('testSchTally')
var { dbClient } = require("wyseman")
const { host, cid0, user0, user1, agent0, agent1, aKey0, aKey1 } = require('./def-users')
var userListen = 'mychips_user_' + user0
var agentListen = 'mychips_agent_' + agent0		//And his agent process
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
      , s = `insert into mychips.tallies (tally_ent, tally_uuid, contract, comment, part_cert)
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

  it("User request to promote tally to offer (draft -> userDraft)", function(done) {
    let sql = uSql(`request = 'offer', hold_sig = 'Adam Signature'`, user0, 1)
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
//log.debug("Sql:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'userDraft')
      _done()
    })
    busA.register('pa', (msg) => {		//Listen for message to agent process
      assert.equal(msg.target, 'tally')
      assert.equal(msg.action, 'userDraft')
      let obj = msg.object			//;log.debug("A obj:", obj)
      assert.ok(!!obj)
      assert.ok(!!obj.uuid)			//A tally attached
      interTest = msg				//Save original tally object
log.debug("Object:", msg.object)
      busA.register('pa')
      _done()
    })
  })

  it("Agent transmits, confirms change to offer (userDraft -> userProffer)", function(done) {
    let logic = {context: ['userDraft'], update: {status: 'offer'}}
      , { cid, agent } = interTest.from
      , msg = {to: {cid, agent}, object: interTest.object}
      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'userProffer')
      done()
    })
  })

  it("Save userProffer tally record for later testing", function(done) {
    dbA.query(save('userProffer'), (e) => {if (e) done(e); else done()})
  })

  var peerProfferGo = function(done) {
    let sign = {foil: 'James Signature', stock:null}		//Altered and signed by James
      , object = Object.assign({}, interTest.object, {sign})
      , logic = {context: ['null','void','userProffer','peerProffer'], upsert: true}
      , { cid, agent } = interTest.from
      , msg = {to: {cid, agent}, object}
      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'peerProffer')
      done()
    })
  }

  it("Agent receives alternative draft (userProffer -> peerProffer)", function(done) {peerProfferGo(done)})
  
  it("User request to promote tally to offer (peerProffer -> userVoid)", function(done) {
    let sql = uSql(`request = 'void', hold_sig = null`, user0, 1)
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
//log.debug("Sql:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'userVoid')
      _done()
    })
    busA.register('pa', (msg) => {		//Listen for message to agent process
//log.debug("sign:", msg.object.sign)
      assert.equal(msg.target, 'tally')
      assert.equal(msg.action, 'userVoid')
      busA.register('pa')
      _done()
    })
  })

  it("Agent transmits, confirms change to void (userVoid -> void)", function(done) {
    let logic = {context: ['userVoid'], update: {status: 'void'}}
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
  it("Agent receives signed offer (<ex nihilo> -> peerProffer)", function(done) {peerProfferGo(done)})

  it("Restore void tally", function(done) {
    dbA.query(rest('void'), (e) => {if (e) done(e); else done()})
  })
  it("Agent receives alternative draft (void -> peerProffer)", function(done) {peerProfferGo(done)})

  it("Save peerProffer tally record for later testing", function(done) {
    dbA.query(save('peerProffer'), (e) => {if (e) done(e); else done()})
  })

  it("Restore userProffer tally", function(done) {
    dbA.query(rest('userProffer'), (e) => {if (e) done(e); else done()})
  })
  it("Peer rejects tally (userProffer -> void)", function(done) {
    let object = Object.assign({}, interTest.object)
      , logic = {context: ['userProffer'], update: {status: 'void'}}
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

  it("Restore userProffer tally", function(done) {
    dbA.query(rest('userProffer'), (e) => {if (e) done(e); else done()})
  })

  it("Peer accepts tally (userProffer -> open)", function(done) {
    let sign = Object.assign({}, interTest.object.sign, {foil: 'James Signature'})
      , object = Object.assign({}, interTest.object, {sign})
      , logic = {context: ['userProffer'], upsert: true, update: {status: 'open'}}
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

  it("Restore peerProffer tally", function(done) {
    dbA.query(rest('peerProffer'), (e) => {if (e) done(e); else done()})
  })
  it("User modifies peer draft (peerProffer -> userDraft)", function(done) {
    let sql = uSql(`request = 'offer', hold_sig = 'Adam Signature', comment = 'A special condition'`, user0, 1)
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
//log.debug("Sql:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
//log.debug("X:", row.request, row.status, row.hold_sig, row.part_sig)
      assert.equal(row.state, 'userDraft')
      _done()
    })
    busA.register('pa', (msg) => {		//Listen for message to agent process
      assert.equal(msg.target, 'tally')
      assert.equal(msg.action, 'userDraft')
      busA.register('pa')
      _done()
    })
  })

  it("Restore peerProffer tally", function(done) {
    dbA.query(rest('peerProffer'), (e) => {if (e) done(e); done()})
  })

  it("User request to accept draft (peerProffer -> userAccept)", function(done) {
    let sql = uSql(`request = 'open', hold_sig = 'Adam Signature', units_gc = 1`, user0, 1)	//Force chips cache to non-zero
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
//log.debug("Sql M:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'userAccept')
      _done()
    })
    busA.register('pa', (msg) => {		//Listen for message to agent process
      assert.equal(msg.target, 'tally')
      assert.equal(msg.action, 'userAccept')
      busA.register('pa')
      _done()
    })
  })

  it("Agent transmits, confirms change to open (userAccept -> open)", function(done) {
    let logic = {context: ['userAccept'], update: {status: 'open'}}
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

  it("User request to close tally (open -> userClose)", function(done) {
    let sql = uSql(`request = 'close'`, user0, 1)
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
//log.debug("Sql M:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'userClose')
      _done()
    })
    busA.register('pa', (msg) => {		//Listen for message to agent process
      assert.equal(msg.target, 'tally')
      assert.equal(msg.action, 'userClose')
      busA.register('pa')
      _done()
    })
  })

  it("Agent transmits, confirms change to close (userClose -> close)", function(done) {
    let logic = {context: ['userClose'], update: {status: 'close'}}
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

  it("Simulate tally balance going to zero (close -> closed)", function(done) {
    let sql = uSql(`units_gc = 0`, user0, 1)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'closed')
      done()
    })
  })

/*
*/
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{		//Let it flush out before closing
      dbU.disconnect()
      dbA.disconnect()
      done()
      }, 200)
  })
});		//Peer to peer tallies

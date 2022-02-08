//Test tally schema at a basic level; run after impexp, testusers
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// This simulates two users connected through a single DB:
// User1 <-> DB <-> Agent1 <-> Agent2 <-> DB <-> User2
//TODO:
//- Test each state transition of a tally
//- Generates proper signals to agent process
//- Generates proper signals to user process
//- 

const { dbConf, Log, Format, Bus, assert, saveRest, getRow, mkUuid } = require('../settings')
var log = Log('testSchTally')
var { dbClient } = require("wyseman")
const { host, user0, user1, Port0, Port1, agent0, agent1, aKey0, aKey1 } = require('./testusers')
var userListen = 'mychips_user_' + user0
var agentListen = 'mychips_agent_' + agent0		//And his agent process
var interTest = {}			//Pass values from one test to another
var contract = {domain:"mychips.org", name:"standard", version:0.99}
var stateField = 'mychips.tally_state(status,request,hold_sig,part_sig,units_gc) as state'
var save = (tag) => saveRest(tag, 'mychips.tallies')
var rest = (tag) => saveRest(tag, 'mychips.tallies', 'rest')
var uSql = (sets) => Format(`update mychips.tallies ${sets} where tally_ent = %L and tally_seq = %L returning *, ${stateField};`, user0, 1)

describe("Test tally state transitions", function() {
  var busU = new Bus('busU'), busA = new Bus('busA')
  var dbU, dbA

  before('User connection to database', function(done) {
    dbU = new dbClient(new dbConf(log,userListen), (chan, data) => {
      log.trace("Notify from U channel:", chan, "data:", data)
      busU.notify(data)
    }, ()=>{log.info("Test DB user connection established"); done()})
  })

  before('Agent connection to database', function(done) {
    dbA = new dbClient(new dbConf(log,agentListen), (chan, data) => {
      log.trace("Notify from A channel:", chan, "data:", data)
      busA.notify(data)
    }, ()=>{log.info("Test DB agent connection established"); done()})
  })

  it("Build draft tally record (<start> -> draft)", function(done) {
    let comment = 'Sample tally'
      , s = `insert into mychips.tallies (tally_ent, tally_uuid, contract, comment, part_cert)
	    	values(%L,%L,%L,%L,mychips.user_cert(%L)) returning *, ${stateField};`
      , sql = Format(s, user0, mkUuid(user0), contract, comment, user1)
//log.debug("Sql:", sql)
    dbU.query(sql, (e, res) => {if (e) done(e)		//;log.debug("Res:", res)
      let tal = getRow(res, 0)
      assert.equal(tal.version, 1)
      assert.equal(tal.tally_seq, 1)
      assert.equal(tal.status,'draft')
      assert.equal(tal.state,'draft')
      done()
    })
  })

  it("Save draft tally record for later testing", function(done) {
    dbU.query(save('draft'), (e) => {if (e) done(e); done()})
  })

  it("User request to promote tally to offer (draft -> userDraft)", function(done) {
    let sql = uSql(`set request = 'offer', hold_sig = 'Adam Signature'`)
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
//log.debug("Sql:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'userDraft')
      _done()
    })
    busA.register('p0', (data) => {		//Listen for message to agent process
      let msg = JSON.parse(data)		//;log.debug("A bus:", msg)
//log.debug("sign:", msg.object.sign)
      assert.equal(msg.target, 'tally')
      assert.equal(msg.action, 'userDraft')
      let obj = msg.object			//;log.debug("A obj:", obj)
      assert.ok(!!obj)
      assert.ok(!!obj.uuid)			//A tally attached
      interTest = msg				//Pass message to next test
      busA.register('p0')
      _done()
    })
  })

  it("Agent transmits, confirms change to offer (userDraft -> userProffer)", function(done) {
    let logic = {context: ['userDraft'], update: {status: 'offer'}}
      , { cid, agent } = interTest.from
      , msg = {cid, agent, object: interTest.object}
      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'userProffer')
      done()
    })
  })

  it("Save userProffer tally record for later testing", function(done) {
    dbU.query(save('userProffer'), (e) => {if (e) done(e); else done()})
  })

  var peerProfferGo = function(done) {
    let sign = {foil: 'James Signature', stock:null}		//Altered and signed by James
      , object = Object.assign({}, interTest.object, {sign})
      , logic = {context: ['null','void','userProffer','peerProffer'], upsert: true}
      , { cid, agent } = interTest.from
      , msg = {cid, agent, object}
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
    let sql = uSql(`set request = 'void', hold_sig = null`)
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
//log.debug("Sql:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'userVoid')
      _done()
    })
    busA.register('p0', (data) => {		//Listen for message to agent process
      let msg = JSON.parse(data)		//;log.debug("A bus:", msg)
//log.debug("sign:", msg.object.sign)
      assert.equal(msg.target, 'tally')
      assert.equal(msg.action, 'userVoid')
      busA.register('p0')
      _done()
    })
  })

  it("Agent transmits, confirms change to void (userVoid -> void)", function(done) {
    let logic = {context: ['userVoid'], update: {status: 'void'}}
      , { cid, agent } = interTest.from
      , msg = {cid, agent, object: interTest.object}
      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'void')
      done()
    })
  })

  it("Delete tally", function(done) {
    let sql = `delete from mychips.tallies;`
    dbU.query(sql, (e, res) => {if (e) done(e); else done()})
  })
  it("Agent receives signed offer (<ex nihilo> -> peerProffer)", function(done) {peerProfferGo(done)})

  it("Restore void tally", function(done) {
    dbU.query(rest('void'), (e) => {if (e) done(e); else done()})
  })
  it("Agent receives alternative draft (void -> peerProffer)", function(done) {peerProfferGo(done)})

  it("Save peerProffer tally record for later testing", function(done) {
    dbU.query(save('peerProffer'), (e) => {if (e) done(e); else done()})
  })

  it("Restore userProffer tally", function(done) {
    dbU.query(rest('userProffer'), (e) => {if (e) done(e); else done()})
  })
  it("Peer rejects tally (userProffer -> void)", function(done) {
    let object = Object.assign({}, interTest.object)
      , logic = {context: ['userProffer'], update: {status: 'void'}}
      , { cid, agent } = interTest.from
      , msg = {cid, agent, object}
      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'void')
      done()
    })
  })

  it("Restore userProffer tally", function(done) {
    dbU.query(rest('userProffer'), (e) => {if (e) done(e); else done()})
  })

  it("Peer accepts tally (userProffer -> open)", function(done) {
    let sign = Object.assign({}, interTest.object.sign, {foil: 'James Signature'})
      , object = Object.assign({}, interTest.object, {sign})
      , logic = {context: ['userProffer'], upsert: true, update: {status: 'open'}}
      , { cid, agent } = interTest.from
      , msg = {cid, agent, object}
      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'open')
      done()
    })
  })

  it("Restore peerProffer tally", function(done) {
    dbU.query(rest('peerProffer'), (e) => {if (e) done(e); else done()})
  })

  it("User modifies peer draft (peerProffer -> userDraft)", function(done) {
    let sql = uSql(`set request = 'offer', hold_sig = 'Adam Signature', comment = 'A special condition'`)
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
//log.debug("Sql:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
//log.debug("X:", row.request, row.status, row.hold_sig, row.part_sig)
      assert.equal(row.state, 'userDraft')
      _done()
    })
    busA.register('p0', (data) => {		//Listen for message to agent process
      let msg = JSON.parse(data)		//;log.debug("A bus:", msg)
      assert.equal(msg.target, 'tally')
      assert.equal(msg.action, 'userDraft')
      busA.register('p0')
      _done()
    })
  })

  it("Restore peerProffer tally", function(done) {
    dbU.query(rest('peerProffer'), (e) => {if (e) done(e); else done()})
  })

  it("User request to accept draft (peerProffer -> userAccept)", function(done) {
    let sql = uSql(`set request = 'open', hold_sig = 'Adam Signature', units_gc = 1`)	//Force chips cache to non-zero
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
//log.debug("Sql M:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'userAccept')
      _done()
    })
    busA.register('p0', (data) => {		//Listen for message to agent process
      let msg = JSON.parse(data)		//;log.debug("A bus:", msg)
      assert.equal(msg.target, 'tally')
      assert.equal(msg.action, 'userAccept')
      interTest = msg				//Pass message to next test
      busA.register('p0')
      _done()
    })
  })

  it("Agent transmits, confirms change to open (userAccept -> open)", function(done) {
    let logic = {context: ['userAccept'], update: {status: 'open'}}
      , { cid, agent } = interTest.from
      , msg = {cid, agent, object: interTest.object}
      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'open')
      done()
    })
  })

  it("Save open tally record for later testing", function(done) {
    dbU.query(save('open'), (e) => {if (e) done(e); else done()})
  })

  it("User request to close tally (open -> userClose)", function(done) {
    let sql = uSql(`set request = 'close'`)
      , dc = 2; _done = () => {if (!--dc) done()}	//2 _done's to be done
//log.debug("Sql M:", sql)
    dbU.query(sql, null, (e, res) => {if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'userClose')
      _done()
    })
    busA.register('p0', (data) => {		//Listen for message to agent process
      let msg = JSON.parse(data)		//;log.debug("A bus:", msg)
      assert.equal(msg.target, 'tally')
      assert.equal(msg.action, 'userClose')
      busA.register('p0')
      _done()
    })
  })

  it("Agent transmits, confirms change to close (userClose -> close)", function(done) {
    let logic = {context: ['userClose'], update: {status: 'close'}}
      , { cid, agent } = interTest.from
      , msg = {cid, agent, object: interTest.object}
      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'close')
      done()
    })
  })

  it("Restore open tally", function(done) {
    dbU.query(rest('open'), (e) => {if (e) done(e); else done()})
  })
  it("Peer requests tally close (open -> close)", function(done) {
    let object = {uuid: interTest.object.uuid}		//Minimal object
      , logic = {context: ['open'], update: {status: 'close'}}
      , { cid, agent } = interTest.from
      , msg = {cid, agent, object}
      , sql = Format(`select mychips.tally_process(%L,%L) as state;`, msg, logic)
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => { if (e) done(e)	//;log.debug("res:", res.rows[0]);
      let row = getRow(res, 0)
      assert.equal(row.state, 'close')
      done()
    })
  })

  it("Simulate tally balance going to zero (close -> closed)", function(done) {
    let sql = uSql(`set units_gc = 0`)
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
      }, 200)
    done()
  })
});		//Peer to peer tallies

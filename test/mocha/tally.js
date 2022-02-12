//Test tally initialization sequence; Run only after impexp, testusers
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// This simulates two users connected through a single DB or two different DBs:
// User1 <-> DB <-> Agent1 <-> Agent2 <-> DB <-> User2
// User1 <-> DB1 <-> Agent1 <-> Agent2 <-> DB2 <-> User2
//TODO:
//X- Give ticket info to other peer
//X- Have them connect via noise module using the ticket
//- Test for one-time connection, token no longer valid
//- Test for reusable token, tally is cloned, token still valid
//- 

const { dbConf, Log, Format, Bus, assert, getRow, mkUuid } = require('../settings')
var log = Log('testTally')
var { dbClient } = require("wyseman")
const PeerCont = require("../../lib/peer2peer")
const PeerNoise = require("../../lib/peernoise")
const {host,user0,user1,cid0,cid1,Port0,Port1,agent0,agent1,aCon0,aCon1} = require('./testusers')
const {user2,cid2,Port2,agent2,aCon2,db2Conf} = require('./user2')
var contract = {domain:"mychips.org", name:"deluxe", version:1.0}
var {stateField, uSql, save, rest} = require('./def-tally')
var interTest = {}			//Pass values from one test to another

//Establish tally between two users
var Suite1 = function({sites, dbcO, dbcS, dbcSO, dbcSS, cidO, cidS, userO, userS, agentO, agentS, aConO, aConS, reuse, preopen}) {
  var serverO, serverS
  var busO = new Bus('busO'), busS = new Bus('busS')
  var dbO, dbS
  var seqO = reuse ? 2 : 1

  before('Connection 0 to test database', function(done) {	//Emulate originator user
    dbO = new dbClient(dbcO, (chan, data) => {
      log.trace("Notify 0 from channel:", chan, "data:", data)
      busO.notify(JSON.parse(data))
    }, ()=>{log.info("Main test DB connection 0 established"); done()})
  })

  before('Connection 1 to test database', function(done) {	//Emulate subject user
    dbS = new dbClient(dbcS, (chan, data) => {
      log.trace("Notify 1 from channel:", chan, "data:", data)
      busS.notify(JSON.parse(data))
    }, ()=>{log.info("Main test DB connection 1 established"); done()})
  })

  before('Launch two peer servers', function(done) {
    serverO = new PeerCont(aConO, dbcSO)		//Smith
    serverS = new PeerCont(aConS, dbcSS)		//Madison
    done()
  })

  it("Initialize DB", function(done) {
    let sql = `begin;
        delete from mychips.tallies;
        update mychips.users set _last_tally = 0; commit`
      , dc = 2; _done = () => {if (!--dc) done()}	//dc _done's to be done
    dbO.query(sql, (e) => {if (e) done(e); _done()})
    dbS.query(sql, (e) => {if (e) done(e); _done()})
  })

  if (preopen) it("Initiate a noise connection between agents", function(done) {
    let pnO = serverO.peerNoise
      , {cid, agent, host, port} = aConS
      , msg = {to: {cid:cidS, agent:agentS, host:aConS.host, port:aConS.port}, text:'Hi!'}
//log.debug('Presend:', cidS, agentS)
    pnO.send(msg, ()=>{
//log.debug('Success!', pnO.connections.size())
      assert.equal(pnO.connections.size(), 1)	//one open connection
      done()
    }, ()=>{done('Failed to open noise connection')})
  })

  it("Originator builds tally template and token", function(done) {
//    let uuid = mkUuid(cidO)
    let s1 = Format('insert into mychips.tallies (tally_ent, contract) values(%L,%L)', userO, contract)
      , sql = `with row as (${s1} returning tally_ent, tally_seq, ${reuse || 'false'})
          insert into mychips.tokens (token_ent, tally_seq, reuse) select * from row returning *;
          select * from mychips.tallies_v where tally_ent = '${userO}' and tally_seq = 1;
          select token,expires,chad from mychips.tokens_v;`
log.debug("Sql:", sql)
    dbO.query(sql, (e, res) => {if (e) done(e)		//;log.debug("res:", res)
      assert.equal(res.length, 3)
      assert.equal(res[0].rowCount, 1)
      let tok = res[0].rows[0]
      assert.equal(tok.token_ent, userO)
      assert.equal(tok.token_seq, 1)
      assert.equal(tok.tally_seq, 1)
      assert.equal(tok.token.length, 32)	//MD5
      let tal = res[1].rows[0]
//log.debug("Talley:", tal)
      assert.ok(!!tal.tally_uuid)
      assert.ok(!tal.part_ent)
      assert.equal(tal.status,'draft')
      assert.equal(tal.tally_type,'stock')
      assert.equal(tal.hold_cid,cidO)
      assert.equal(tal.hold_agent,agentO)
      let ticket = res[2].rows[0]
//log.debug("Ticket:", ticket)
      interTest = ticket
      done()
    })
  })

  it("Subject asks his server to request the proposed tally", function(done) {
    let sql = Format('select mychips.ticket_process(%L,%L)', interTest, userS)
      , dc = 2; _done = () => {if (!--dc) done()}	//dc _done's to be done
//log.debug("Sql:", sql)
    dbS.query(sql, null, (e, res) => { if (e) done(e)
      let row = getRow(res, 0)
//log.debug("row:", row);
      assert.ok(row.ticket_process)
      _done()
    })
    busO.register('po', (msg) => {	//Originator is prompted to sign the tally
log.debug("msg:", msg)
      assert.equal(msg.entity, userO)
      assert.equal(msg.state, 'draft')
      assert.equal(msg.sequence, seqO)
      let tally = msg.object
        , stock = tally.stock
        , foil = tally.foil
log.debug("tally:", tally, "S:", tally.stock, "F:", tally.foil)
      assert.equal(stock.cert.chad.cid, cidO)
      assert.equal(stock.cert.chad.agent, agentO)
      assert.equal(foil.cert.chad.cid, cidS)
      assert.equal(foil.cert.chad.agent, agentS)
//log.debug("sign:", tally.sign)
      assert.ok(!tally.sign.stock)
      assert.ok(!tally.sign.foil)
      busO.register('po')
      _done()
    })
  })

  it("Originator approves, signs the proposed tally", function(done) {
    let uuid = mkUuid(cidO)			//Make a real UUID for this user/tally
      , sql = uSql('tally_uuid = %L, request = %L, hold_sig = %L', uuid, 'offer', 'Originator Signature', userO, seqO)
      , dc = 3; _done = () => {if (!--dc) done()}	//dc _done's to be done
log.debug("Sql:", sql)
    dbO.query(sql, (err, res) => { if (err) done(err)
      let row = getRow(res, 0)			//;log.debug("row:", row);
      assert.equal(row.request, 'offer')
      assert.equal(row.status, 'draft')
      assert.equal(row.state, 'userDraft')
      _done()
    })
    busS.register('ps', (msg) => {		//Subject is sent the proposed tally
      assert.equal(msg.entity, userS)
      assert.equal(msg.state, 'peerProffer')
      let tally = msg.object
        , stock = tally.stock
        , foil = tally.foil
//log.debug("tally:", tally, tally.stock.cert.chad)
      assert.equal(stock.cert.chad.cid, cidO)
      assert.equal(stock.cert.chad.agent, agentO)
      assert.equal(foil.cert.chad.cid, cidS)
      assert.equal(foil.cert.chad.agent, agentS)
//log.debug("sign:", tally.sign)
      assert.ok(!!tally.sign.stock)
      assert.ok(!tally.sign.foil)
      assert.ok(!tally.part_ent)			//Haven't linked partner yet
      interTest = tally
      busS.register('ps')
      _done()
    })
    busO.register('po', (msg) => {		//Originator is sent the close request
//log.debug("msg:", msg, msg.object.sign)
      assert.equal(msg.entity, userO)
      assert.equal(msg.state, 'userProffer')
      assert.ok(!!msg.object.sign.stock)
      assert.ok(!msg.object.sign.foil)
      busO.register('po')
      _done()
    })
  })

  it("Save proffered tallies for later testing", function(done) {
    let dc = sites; _done = () => {if (!--dc) done()}
    dbO.query(save('proffer'), (e) => {if (e) done(e); _done()})
    if (sites > 1) dbS.query(save('proffer'), (e) => {if (e) done(e); _done()})
  })

  it("Subject rejects the proposed tally", function(done) {
    let sql = uSql('request = %L, hold_sig = %L', 'void', null, userS, 1)
      , dc = 3; _done = () => {if (!--dc) done()}	//dc _done's to be done
//log.debug("Sql:", sql)
    dbS.query(sql, (err, res) => { if (err) done(err)
      let row = getRow(res, 0)			//;log.debug("row:", row);
      assert.equal(row.request, 'void')
      assert.equal(row.status, 'offer')
      assert.equal(row.state, 'userVoid')
      _done()
    })
    busO.register('po', (msg) => {		//Originator is sent the rejection
      assert.equal(msg.entity, userO)
      assert.equal(msg.state, 'void')
      busO.register('po')
      _done()
    })
    busS.register('ps', (msg) => {		//Subject is notified of open
//log.debug("msg:", msg, msg.object.sign)
      assert.equal(msg.entity, userS)
      assert.equal(msg.state, 'void')
      busS.register('ps')
      _done()
    })
  })

  it("Restore proffered tallies", function(done) {
    let dc = sites; _done = () => {if (!--dc) done()}
    dbO.query(rest('proffer'), (e) => {if (e) done(e); else done()})
    if (sites > 1) dbS.query(rest('proffer'), (e) => {if (e) done(e); _done()})
  })

  it("Subject counters the proposed tally", function(done) {
    let sql = uSql('request = %L, hold_sig = %L', 'offer', 'Subject Signature', userS, 1)
      , dc = 3; _done = () => {if (!--dc) done()}	//dc _done's to be done
//log.debug("Sql:", sql)
    dbS.query(sql, (err, res) => { if (err) done(err)
      let row = getRow(res, 0)			//;log.debug("row:", row);
      assert.equal(row.request, 'offer')
      assert.equal(row.status, 'draft')
      assert.equal(row.state, 'userDraft')
      _done()
    })
    busO.register('po', (msg) => {		//Originator is sent the rejection
      assert.equal(msg.entity, userO)
      assert.equal(msg.state, 'peerProffer')
      busO.register('po')
      _done()
    })
    busS.register('ps', (msg) => {		//Subject is notified of open
//log.debug("msg:", msg, msg.object.sign)
      assert.equal(msg.entity, userS)
      assert.equal(msg.state, 'userProffer')
      busS.register('ps')
      _done()
    })
  })

  it("Restore proffered tallies", function(done) {
    let dc = sites; _done = () => {if (!--dc) done()}
    dbO.query(rest('proffer'), (e) => {if (e) done(e); else done()})
    if (sites > 1) dbS.query(rest('proffer'), (e) => {if (e) done(e); _done()})
  })

  it("Subject accepts the proposed tally", function(done) {
    let sql = uSql('request = %L, hold_sig = %L', 'open', 'Subject Signature', userS, 1)
      , dc = 3; _done = () => {if (!--dc) done()}	//dc _done's to be done
//log.debug("Sql:", sql)
    dbS.query(sql, (err, res) => { if (err) done(err)
      let row = getRow(res, 0)			//;log.debug("row:", row);
      assert.equal(row.request, 'open')
      assert.equal(row.status, 'offer')
      assert.equal(row.state, 'userAccept')
      _done()
    })
    busO.register('po', (msg) => {		//Originator is sent the acceptance
      assert.equal(msg.entity, userO)
      assert.equal(msg.state, 'open')
      busO.register('po')
      _done()
    })
    busS.register('ps', (msg) => {		//Subject is notified of open
      assert.equal(msg.entity, userS)
      assert.equal(msg.state, 'open')
      busS.register('ps')
      _done()
    })
  })

  it("Simulate non-zero tally balance", function(done) {
    let dc = 2; _done = () => {if (!--dc) done()}	//dc _done's to be done
    dbO.query(uSql('units_gc = 1', userO, seqO), (e, res) => { if (e) done(e); _done()})
    dbS.query(uSql('units_gc = 1', userS, 1), (e, res) => { if (e) done(e); _done()})
  })

  it("Subject requests to close the proposed tally", function(done) {
    let sql = uSql('request = %L', 'close', userS, 1)
      , dc = 3; _done = () => {if (!--dc) done()}	//dc _done's to be done
//log.debug("Sql:", sql)
    dbS.query(sql, (err, res) => { if (err) done(err)
      let row = getRow(res, 0)			//;log.debug("row:", row);
      assert.equal(row.request, 'close')
      assert.equal(row.status, 'open')
      assert.equal(row.state, 'userClose')
      _done()
    })
    busO.register('po', (msg) => {		//Originator is sent the close request
      assert.equal(msg.entity, userO)
      assert.equal(msg.state, 'close')
      busS.register('po')
      _done()
    })
    busS.register('ps', (msg) => {		//Subject is notified of open
//log.debug("msg:", msg, msg.object.sign)
      assert.equal(msg.entity, userS)
      assert.equal(msg.state, 'close')
      assert.ok(!!msg.object.sign.stock)
      assert.ok(!!msg.object.sign.foil)
      busS.register('ps')
      _done()
    })
  })

  it("Simulate tally balance going to zero (close -> closed)", function(done) {
    let dc = 2; _done = () => {if (!--dc) done()}	//dc _done's to be done
    dbO.query(uSql('units_gc = 0', userO, seqO), (e, res) => { if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row);
      assert.equal(row.state, 'closed')
      _done()
    })
    dbS.query(uSql('units_gc = 0', userS, 1), (e, res) => { if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row);
      assert.equal(row.state, 'closed')
      _done()
    })
  })

/*
*/
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{		//Let everything flush out before closing
      dbO.disconnect()
      dbS.disconnect()
      serverO.close()
      serverS.close()
      done()
      }, 200)
  })
}		//Suite 1

// Main
// ----------------------------------------------------------------------------
describe("Tally peer-to-peer testing", function() {
  let configS = {		//Two users on name host
    sites:1,
    cidO:cid0, cidS:cid1, userO:user0, userS:user1, aConO:aCon0, aConS:aCon1, agentO:agent0, agentS:agent1,
    dbcO: new dbConf(log, 'mychips_user_p1000'), 
    dbcS: new dbConf(log, 'mychips_user_p1001'),
    dbcSO: new dbConf(),
    dbcSS: new dbConf()
  }
  let configD = {		//Two users on different hosts
    sites:2,
    cidO:cid0, cidS:cid2, userO:user0, userS:user2, aConO:aCon0, aConS:aCon2, agentO:agent0, agentS:agent2,
    dbcO: new dbConf(log, 'mychips_user_p1000'), 
    dbcS: new db2Conf(log, 'mychips_user_p1002'),
    dbcSO: new dbConf(),
    dbcSS: new db2Conf()
  }
  let configR = {		//Reusable token across open channel
    sites:2,
    cidO:cid2, cidS:cid1, userO:user2, userS:user1, aConO:aCon2, aConS:aCon1, agentO:agent2, agentS:agent1,
    dbcO: new db2Conf(log, 'mychips_user_p1002'), 
    dbcS: new dbConf(log, 'mychips_user_p1001'),
    dbcSO: new db2Conf(),
    dbcSS: new dbConf(),
    reuse: true,
    preopen: true
  }

  describe("Establish tally between two users on same site", function() {Suite1(configS)})
  describe("Establish tally between two users on different sites", function() {Suite1(configD)})
  describe("Establish reusable tally over open connection", function() {Suite1(configR)})
})

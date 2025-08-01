//Test tally initialization sequence; run
//After: user2
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// This simulates two users connected through a single DB or two different DBs:
// User1 <-> DB <-> Agent1 <-> Agent2 <-> DB <-> User2
// User1 <-> DB1 <-> Agent1 <-> Agent2 <-> DB2 <-> User2
//TODO:
//- Test for one-time connection, token no longer valid
//- Test for reusable token, tally is cloned, token still valid
//- 
const { dbConf, testLog, Format, Bus, assert, getRow, mkUuid, dbClient, SubCrypto, Stringify, peerTest, markLogs, libModule, sinon} = require('../common')
const log = testLog(__filename)
const crypto = new SubCrypto(log)
const {host,user0,user1,user2,cuid0,cuid1,cuid2,agent0,agent1,agent2,aCon0,aCon1,aCon2,db2Conf} = require('../def-users')
const contract = {domain:"mychips.org", name:"deluxe", version:1.0}
const {uSql, sSql, save, rest} = require('./def-tally')
let interTest = {}			//Pass values from one test to another

//Establish tally between two users
var Suite1 = function({sites, dbcO, dbcS, dbcSO, dbcSS, cuidO, cuidS, userO, userS, agentO, agentS, aConO, aConS, reuse, preopen, saveName}) {
  let serverO, serverS
  let busO = new Bus('busO'), busS = new Bus('busS')
  let dbO, dbS
  let seqS = 1, seqO = reuse ? 2 : 1
  
  const getSignature = function(db, user, seq, done) {
    let sql = sSql('t.json_core, u.user_cmt', user, seq)	//;log.debug('sql:', sql)
    db.query(sql, (err, res) => { if (err) done(err)
      let row = getRow(res, 0)				//;log.debug("row:", row)
        , key = row.user_cmt				//;log.debug("key:", key)
        , message = Stringify(row.json_core)		//;log.debug('JSON:', message.slice(0,40))

      assert.ok(row.json_core)
      crypto.sign(key, message).then(sign => {
        let textSign = Buffer.from(sign).toString('base64url')
        assert.ok(textSign)			//;log.debug('sign:', textSign)
        interTest.sign = textSign
        done()
      })
    })
  }

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
    serverO = new peerTest(aConO, dbcSO)		//Smith
    serverS = new peerTest(aConS, dbcSS)		//Madison
    done()
  })

  it("Initialize DB", function(done) {
    let sql = `begin;
        delete from mychips.tallies;
        update mychips.users set _last_tally = 0; commit`
      , dc = 2, _done = () => {if (!--dc) done()}	//dc _done's to be done
    dbO.query(sql, (e) => {if (e) done(e); _done()})
    dbS.query(sql, (e) => {if (e) done(e); _done()})
  })

  if (preopen) it("Initiate a noise connection between agents", function(done) {
    let pnO = serverO.peerNoise
      , {cuid, agent, host, port} = aConS
      , msg = {to: {cuid:cuidS, agent:agentS, host:aConS.host, port:aConS.port}, text:'Hi!'}
//log.debug('Presend:', cuidS, agentS)
    pnO.send(msg, ()=>{
//log.debug('Success!', pnO.connections.size())
      assert.equal(pnO.connections.size(), 1)	//one open connection
      done()
    }, ()=>{done('Failed to open noise connection')})
  })

  it("Originator builds tally template and token", function(done) {
    let s1 = Format('insert into mychips.tallies_v (tally_ent, contract) values(%L,%L)', userO, contract)
      , sql = `with row as (${s1} returning tally_ent, tally_seq, ${reuse || 'false'})
          insert into mychips.tokens (token_ent, tally_seq, reuse) select * from row returning *;
          select * from mychips.tallies_v where tally_ent = '${userO}' and tally_seq = 1;
          select token,expires,chad from mychips.tokens_v;`
//log.debug("Sql:", sql)
    dbO.query(sql, (e, res) => {if (e) done(e)		//;log.debug("res:", res)
      assert.equal(res.length, 3)
      assert.equal(res[0].rowCount, 1)
      let tok = res[0].rows[0]
      assert.equal(tok.token_ent, userO)
      assert.equal(tok.token_seq, 1)
      assert.equal(tok.tally_seq, 1)
      assert.equal(tok.token.length, 32)	//MD5
      let tal = res[1].rows[0]			//;log.debug("Talley:", tal)
      assert.ok(!!tal.tally_uuid)
      assert.ok(!tal.part_ent)
      assert.equal(tal.status,'draft')
      assert.equal(tal.tally_type,'stock')
      assert.equal(tal.hold_cuid,cuidO)
      assert.equal(tal.hold_agent,agentO)
      let ticket = res[2].rows[0]		//;log.debug("Ticket:", ticket)
      interTest = ticket
      done()
    })
  })

  it("Subject asks his server to request the proposed tally", function(done) {
    let sql = Format('select mychips.ticket_process(%L,%L)', interTest, userS)
      , dc = 2, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql)
    dbS.query(sql, null, (e, res) => { if (e) done(e)
      let row = getRow(res, 0)		//;log.debug("row:", row)
      assert.ok(row.ticket_process)
      _done()
    })
    busO.register('po', (msg) => {	//;log.debug("msg:", msg)
      assert.equal(msg.entity, userO)	//Originator is prompted to sign the tally
      assert.equal(msg.state, 'P.draft')
      assert.equal(msg.sequence, seqO)
      let tally = msg.object
        , stock = tally.stock
        , foil = tally.foil		//;log.debug("tally:", tally, "S:", tally.stock, "F:", tally.foil)
      assert.equal(stock.cert.chad.cuid, cuidO)
      assert.equal(stock.cert.chad.agent, agentO)
      assert.equal(foil.cert.chad.cuid, cuidS)
      assert.equal(foil.cert.chad.agent, agentS)
      assert.ok(!tally.sign.stock)	//;log.debug("sign:", tally.sign)
      assert.ok(!tally.sign.foil)
      _done()
    })
  })

  it("Make a real UUID for the proposed tally", function(done) {
    let uuid = mkUuid(cuidO, agent0)
      , sql = uSql('tally_uuid = %L', uuid, userO, seqO)
//log.debug("Sql:", sql)
    dbO.query(sql, (err, res) => { if (err) done(err)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.tally_uuid, uuid)
      done()
    })
  })

  it("Generate tally signature", function(done) {
    getSignature(dbO, userO, seqO, done)
  })

  it("Originator approves, signs the proposed tally", function(done) {
    let sql = uSql('request = %L, hold_sig = %L', 'offer', interTest.sign, userO, seqO)
      , dc = 3, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql)
    dbO.query(sql, (err, res) => { if (err) done(err)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.request, 'offer')
      assert.equal(row.status, 'draft')
      assert.equal(row.state, 'draft.offer')
      _done()
    })
    busS.register('ps', (msg) => {		//Subject is sent the proposed tally
      assert.equal(msg.entity, userS)		//;log.debug("S msg:", msg)
      assert.equal(msg.state, 'P.offer')
      let tally = msg.object			//;log.debug("S tally:", tally, tally.stock.cert.chad)
        , stock = tally.stock
        , foil = tally.foil
      assert.equal(stock.cert.chad.cuid, cuidO)
      assert.equal(stock.cert.chad.agent, agentO)
      assert.equal(foil.cert.chad.cuid, cuidS)
      assert.equal(foil.cert.chad.agent, agentS)
      assert.ok(!!tally.sign.stock)		//;log.debug("sign:", tally.sign)
      assert.ok(!tally.sign.foil)
      assert.ok(!tally.part_ent)		//Haven't linked partner yet
      interTest = tally
      _done()
    })
    busO.register('po', (msg) => {		//;log.debug("O msg:", msg, msg.object.sign)
      assert.equal(msg.entity, userO)		//Originator is sent the close request
      assert.equal(msg.state, 'H.offer')
      assert.ok(!!msg.object.sign.stock)
      assert.ok(!msg.object.sign.foil)
      _done()
    })
  })

  it("Save proffered tallies for later testing", function(done) {
    let dc = sites, _done = () => {if (!--dc) done()}
    dbO.query(save('Hoffer'), (e) => {if (e) done(e); _done()})
    if (sites > 1) dbS.query(save('Hoffer'), (e) => {if (e) done(e); _done()})
  })

  it("Subject rejects the proposed tally", function(done) {
    let sql = uSql('request = %L, hold_sig = %L', 'void', null, userS, 1)
      , dc = 3, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql)
    dbS.query(sql, (err, res) => { if (err) done(err)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.request, 'void')
      assert.equal(row.status, 'offer')
      assert.equal(row.state, 'offer.void')
      _done()
    })
    busO.register('po', (msg) => {		//;log.debug("O msg:", msg, msg.object.sign)
      assert.equal(msg.entity, userO)		//Originator is sent the rejection
      assert.equal(msg.state, 'void')
      _done()
    })
    busS.register('ps', (msg) => {		;log.debug("S msg:", msg, msg.object.sign)
      assert.equal(msg.entity, userS)		//Subject is notified of open
      assert.equal(msg.state, 'void')
      _done()
    })
  })

  it("Restore proffered tallies", function(done) {
    let dc = sites, _done = () => {if (!--dc) done()}
    dbO.query(rest('Hoffer'), (e) => {if (e) done(e); else _done()})
    if (sites > 1) dbS.query(rest('Hoffer'), (e) => {if (e) done(e); _done()})
  })

  it("Generate tally signature", function(done) {
    getSignature(dbS, userS, 1, done)
  })

  it("Subject will revise the proposed tally", function(done) {
    let sql = uSql('request = %L', 'draft', userS, 1)
      , dc = 3, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql)
    dbS.query(sql, (err, res) => { if (err) done(err)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.request, 'draft')
      assert.equal(row.status, 'offer')
      assert.equal(row.state, 'offer.draft')
      assert.equal(row.tally_type, 'foil')
      _done()
    })
    busO.register('po', (msg) => {		//;log.debug("O msg:", msg, msg.object)
      assert.equal(msg.entity, userO)		//Originator is sent a notification only
      assert.equal(msg.state, 'H.offer')
      assert.equal(msg.reason, 'draft')		//Noting the subject is re-drafting
      assert.equal(msg.object?.revision, 1)
      _done()
    })
    busS.register('ps', (msg) => {		//;log.debug("S msg:", msg, msg.object)
      assert.equal(msg.entity, userS)		//Subject is notified of draft mode
      assert.equal(msg.state, 'P.draft')
      assert.equal(msg.object?.revision, 2)
      _done()
    })
  })

  it("Subject revises draft tally", function(done) {
    let cmt = 'Revised offer'
      , type = 'stock'
      , sql = uSql('comment = %L, tally_type = %L', cmt, type, userS, 1)
//log.debug("Sql:", sql)
    dbS.query(sql, (err, res) => { if (err) done(err)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.strictEqual(row.request, null)
      assert.equal(row.status, 'draft')
      assert.equal(row.tally_type, type)
      assert.equal(row.comment, cmt)
      interTest.lastCmt = cmt
      done()
    })
  })
  
  it("Generate tally signature", function(done) {
    getSignature(dbS, userS, 1, done)
  })

  it("Subject counters with revised tally", function(done) {
    let sql = uSql('request = %L, hold_sig = %L', 'offer', interTest.sign, userS, 1)
      , dc = 3, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql)
    dbS.query(sql, (err, res) => { if (err) done(err)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.request, 'offer')
      assert.equal(row.status, 'draft')
      assert.equal(row.state, 'draft.offer')
      _done()
    })
    busO.register('po', (msg) => {		//;log.debug("O msg:", JSON.stringify(msg))
      assert.equal(msg.entity, userO)		//Originator is sent the rejection
      assert.equal(msg.state, 'P.offer')
      assert.equal(msg.object?.revision, 2)
      assert.equal(msg.object?.memo, interTest.lastCmt)
      _done()
    })
    busS.register('ps', (msg) => {		//;log.debug("S msg:", JSON.stringify(msg))
      assert.equal(msg.entity, userS)		//Subject is notified of open
      assert.equal(msg.state, 'H.offer')
      assert.equal(msg.object?.revision, 2)
      assert.equal(msg.object?.memo, interTest.lastCmt)
      _done()
    })
  })

  it("Restore proffered tallies", function(done) {
    let dc = sites, _done = () => {if (!--dc) done()}
    dbO.query(rest('Hoffer'), (e) => {if (e) done(e); else _done()})
    if (sites > 1) dbS.query(rest('Hoffer'), (e) => {if (e) done(e); _done()})
  })

  it("Generate tally signature", function(done) {
    getSignature(dbS, userS, 1, done)
  })

  it("Subject accepts the proposed tally", function(done) {
    let sql = uSql('request = %L, hold_sig = %L', 'open', interTest.sign, userS, 1)
      , dc = 3, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql)
    dbS.query(sql, (err, res) => { if (err) done(err)
      let row = getRow(res, 0)			;log.debug("row:", row)
      assert.equal(row.request, 'open')
      assert.equal(row.status, 'offer')
      assert.equal(row.state, 'offer.open')
      assert.strictEqual(row.chain_conf, null)
      _done()
    })
    busO.register('po', (msg) => {		//Originator is sent the acceptance
      assert.equal(msg.entity, userO)
      assert.equal(msg.state, 'open')
      _done()
    })
    busS.register('ps', (msg) => {		//Subject is notified of open
      assert.equal(msg.entity, userS)
      assert.equal(msg.state, 'open')
      _done()
    })
  })

  it("Wait for consensus to settle", function(done) {setTimeout(done, 250)})

  it("Verify chain confirmation initialized", function(done) {
    let sql = `select state,chain_conf from mychips.tallies_v where tally_ent = $1 and tally_seq = $2;`
      , dc = 2, _done = () => {if (!--dc) done()}
    dbO.query(sql, [userO, seqO], (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("O row:", row)
      assert.equal(row.chain_conf, 0)
      _done()
    })
    dbS.query(sql, [userS, seqS], (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("S row:", row)
      assert.equal(row.chain_conf, 0)
      _done()
    })
  })

  if (saveName) it("Save open tallies for later chit test", function(done) {
    let dc = sites, _done = () => {if (!--dc) done()}
    dbO.query(save(saveName), (e) => {if (e) done(e); _done()})
    if (sites > 1) dbS.query(save(saveName), (e) => {if (e) done(e); _done()})
  })

  it("Resend an open tally", function(done) {
    let sql = uSql('request = %L', 'open', userS, 1)
//log.debug("Sql:", sql)
    dbS.query(sql, (err, res) => { if (err) done(err)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.request, 'open')
      assert.equal(row.status, 'open')
      assert.equal(row.state, 'open.open')
      done()
    })
  })

  it("Wait for status to settle", function(done) {setTimeout(done, 250)})

  it("Verify request flag got reset", function(done) {
    let sql = `select request,state,chain_conf from mychips.tallies_v where tally_ent = $1 and tally_seq = $2;`
    dbS.query(sql, [userS, seqS], (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("S row:", row)
      assert.strictEqual(row.request, null)
      assert.equal(row.state, 'open')
      assert.equal(row.chain_conf, 0)
      done()
    })
  })

  it("Restore proffered tallies", function(done) {
    let dc = sites, _done = () => {if (!--dc) done()}
    dbO.query(rest('Hoffer'), (e) => {if (e) done(e); else _done()})
    if (sites > 1) dbS.query(rest('Hoffer'), (e) => {if (e) done(e); _done()})
  })

  it("Subject attempts to accept tally without a signature", function(done) {
    let sql = uSql('request = %L', 'open',  userS, 1)
//log.debug("Sql:", sql)
    dbS.query(sql, (err, res) => {
      assert.ok(err)				//;log.debug("err:", err, err.message)
      assert.ok(err.message)
      let [code, from, to] = err.message.split(' ')
      assert.equal(code, '!mychips.tallies:ISR')
      done()
    })
  })

  it("Subject attempts to accept tally with a bad signature", function(done) {
    let consoleErrorStub = sinon.stub(console, 'error')
    let sql = uSql('request = %L, hold_sig = %L', 'open', 'Invalid signature', userS, 1)
      , dc = 2, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql)
    dbS.query(sql, (err, res) => {
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.request, 'open')
      assert.equal(row.status, 'offer')
      assert.equal(row.state, 'offer.open')
      _done()
    })
    busS.register('ps', (msg) => {		//;log.debug("S msg:", msg, msg.object.sign)
      assert.equal(msg.entity, userS)		//Subject is notified
      assert.equal(msg.reason, 'open')		//Attempt to open
      assert.equal(msg.state, 'P.offer')	//Still stuck in offer state
      consoleErrorStub.restore()
      _done()
    })
  })

  it("Subject attempts to accept tally with unreachable partner", function(done) {
    let consoleErrorStub = sinon.stub(console, 'error')
    let sql = uSql('request = %L, hold_sig = %L', 'open', interTest.sign, userS, 1)
//log.debug("Sql:", sql)
    serverS.failSend = 'fail'			//Force: fail to connect with peer
    dbS.query(sql, (err, res) => {
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.request, 'open')
      assert.equal(row.status, 'offer')
      assert.equal(row.state, 'offer.open')
      setTimeout(() => {consoleErrorStub.restore()}, 250)	//stop lingering errors in packet handling
      done()
    })
  })

  it("Retry properly registered in DB", function(done) {
    let sql = `update mychips.tally_tries
        set last = 'now'::timestamp - '70 minutes'::interval
        where ttry_ent = $1 and ttry_seq = $2 returning *`	//Force timestamp for next test to work
      , parms = [userS, 1]
//log.debug("Sql:", sql, parms)
    dbS.query(sql, parms, (err, res) => {
      let row = getRow(res, 0)			;log.debug("row:", row)
      assert.equal(row.tries, 1)
      done()
    })
  })

  it("Polling request retries tally open transmission", function(done) {
    let sql = 'select mychips.tally_notices() as notices'
      , dc = 2, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql)
    dbS.query(sql, (err, res) => {
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.notices, 1)
      _done()
    })
    busS.register('ps', (msg) => {		//;log.debug("S msg:", msg, msg.object.sign)
      assert.equal(msg.entity, userS)		//Subject is notified
      assert.equal(msg.reason, 'open')		//Attempt to open
      assert.equal(msg.state, 'open')
      _done()
    })
  })

//Obsolete: move to chit testing
//  it("Simulate non-zero tally balance", function(done) {
//    let dc = 2, _done = () => {if (!--dc) done()}
//    dbO.query(uSql('units_c = 1', userO, seqO), (e, res) => { if (e) done(e); _done()})
//    dbS.query(uSql('units_c = 1', userS, 1), (e, res) => { if (e) done(e); _done()})
//  })
//  it("Subject requests to close the proposed tally", function(done) {
//    let sql = uSql('request = %L', 'close', userS, 1)
//      , dc = 3, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql)
//    dbS.query(sql, (err, res) => { if (err) done(err)
//      let row = getRow(res, 0)			//;log.debug("row:", row)
//      assert.equal(row.request, 'close')
//      assert.equal(row.status, 'open')
//      assert.equal(row.state, 'open.close')
//      _done()
//    })
//    busO.register('po', (msg) => {		//Originator is sent the close request
//      assert.equal(msg.entity, userO)
//      assert.equal(msg.state, 'close')
//      _done()
//    })
//    busS.register('ps', (msg) => {		//Subject is notified of open
//log.debug("msg:", msg, msg.object.sign)
//      assert.equal(msg.entity, userS)
//      assert.equal(msg.state, 'close')
//      assert.ok(!!msg.object.sign.stock)
//      assert.ok(!!msg.object.sign.foil)
//      _done()
//    })
//  })
//
//  it("Simulate tally balance going to zero (close -> closed)", function(done) {
//    let dc = 2, _done = () => {if (!--dc) done()}
//    dbO.query(uSql('units_c = 0', userO, seqO), (e, res) => { if (e) done(e)
//      let row = getRow(res, 0)			//;log.debug("row:", row)
//      assert.equal(row.state, 'closed')
//      _done()
//    })
//    dbS.query(uSql('units_c = 0', userS, 1), (e, res) => { if (e) done(e)
//      let row = getRow(res, 0)			//;log.debug("row:", row)
//      assert.equal(row.state, 'closed')
//      _done()
//    })
//  })

//  it("Mark the log files", function(done) {markLogs(dbO, log, done)})
/* */
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
  let config1 = {		//Two users on name host
    sites:1, saveName:'open1',
    cuidO:cuid0, cuidS:cuid1, userO:user0, userS:user1, aConO:aCon0, aConS:aCon1, agentO:agent0, agentS:agent1,
    dbcO: new dbConf(log, 'mu_p1000'), 
    dbcS: new dbConf(log, 'mu_p1001'),
    dbcSO: new dbConf(),
    dbcSS: new dbConf()
  }
  let config2 = {		//Two users on different hosts
    sites:2, saveName:'open2',
    cuidO:cuid0, cuidS:cuid2, userO:user0, userS:user2, aConO:aCon0, aConS:aCon2, agentO:agent0, agentS:agent2,
    dbcO: new dbConf(log, 'mu_p1000'), 
    dbcS: db2Conf(log, 'mu_p1002'),
    dbcSO: new dbConf(),
    dbcSS: db2Conf()
  }
  let config2r = {		//Reusable token across open channel
    sites:2,
    cuidO:cuid2, cuidS:cuid1, userO:user2, userS:user1, aConO:aCon2, aConS:aCon1, agentO:agent2, agentS:agent1,
    dbcO: db2Conf(log, 'mu_p1002'), 
    dbcS: new dbConf(log, 'mu_p1001'),
    dbcSO: db2Conf(),
    dbcSS: new dbConf(),
    reuse: true,
    preopen: true
  }

  describe("Establish tally between two users on same site", function() {Suite1(config1)})
  describe("Establish tally between two users on different sites", function() {Suite1(config2)})
  describe("Establish reusable tally over open connection", function() {Suite1(config2r)})
})

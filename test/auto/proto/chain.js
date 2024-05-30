//Test chit consensus between peers; run
//After: chit
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// This simulates two users connected through a single DB or two different DBs:
// User1 <-> DB <-> Agent1 <-> Agent2 <-> DB <-> User2
// User1 <-> DB1 <-> Agent1 <-> Agent2 <-> DB2 <-> User2
//TODO:
//- 
const { dbConf, testLog, Format, Bus, assert, getRow, mkUuid, dbClient, peerTest, markLogs } = require('../common')
var log = testLog(__filename)
var defTally = require('./def-tally')
var defChit = require('./def-chit')
var {uSql, save, rest} = require('./def-chit')
const {host,user0,user1,user2,cuid0,cuid1,cuid2,agent0,agent1,agent2,aCon0,aCon1,aCon2,db2Conf} = require('../def-users')
var interTest = {}			//Pass values from one test to another

var Suite1 = function({sites, dbcO, dbcS, dbcSO, dbcSS, cuidO, cuidS, userO, userS, agentO, agentS, aConO, aConS, saveName}) {
  var serverO, serverS
  var busO = new Bus('busO'), busS = new Bus('busS')
  var dbO, dbS

  before('Connection 0 to test database', function(done) {	//Emulate originator user
    dbO = new dbClient(dbcO, (chan, data, me) => {
      log.trace("Notify O from channel:", chan, me, "data:", data)
      busO.notify(JSON.parse(data))
    }, ()=>{log.info("Main test DB connection 0 established"); done()})
  })

  before('Connection 1 to test database', function(done) {	//Emulate subject user
    dbS = new dbClient(dbcS, (chan, data, me) => {
      log.trace("Notify S from channel:", chan, me, "data:", data)
      busS.notify(JSON.parse(data))
    }, ()=>{log.info("Main test DB connection 1 established"); done()})
  })

  before('Launch two peer servers', function(done) {	//Don't require real signatures
    serverO = new peerTest(Object.assign(aConO,{test:true}), dbcSO)
    serverS = new peerTest(Object.assign(aConS,{test:true}), dbcSS)
    done()
  })

  it("Restore open tallies", function(done) {
    let dc = sites, _done = () => {if (!--dc) done()}
    dbO.query(defTally.rest(saveName), (e) => {if (e) done(e); else _done()})
    if (sites > 1) dbS.query(defTally.rest(saveName), (e) => {if (e) done(e); _done()})
  })

  it("Restore open chits", function(done) {
    let dc = sites, _done = () => {if (!--dc) done()}
    dbO.query(defChit.rest(saveName), (e) => {if (e) done(e); else _done()})
    if (sites > 1) dbS.query(defChit.rest(saveName), (e) => {if (e) done(e); _done()})
  })

  it("Verify existing tallies/chits in DB", function(done) {
    let sql = `select tally_ent,tally_seq,tally_type,state,chits,chain_conf,ack_hash from mychips.tallies_v where tally_type = $1`
      , dc = 2, _done = () => {if (!--dc) done()}	//dc _done's to be done
    dbO.query(sql, ['stock'], (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("O row:", row)
      assert.equal(row.chits, 2)
      assert.equal(row.chain_conf, 2)
      interTest.talO = row
      _done()
    })
    dbS.query(sql, ['foil'], (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("S row:", row)
      assert.equal(row.chits, 2)
      interTest.talS = row
      _done()
    })
  })
  
  const addChit = function(db, by, value, ent, seq, done) {
    let uuid = mkUuid('cuid', 'agent', Math.random().toString())
      , request = 'good'
      , sign = 'Signature'
      , sql = Format(`insert into mychips.chits_v (chit_ent, chit_seq, chit_uuid, chit_type, issuer, units, request, signature)
          values (%L, %s, %L, 'tran', %L, %s, %L, %L) returning *`, ent, seq, uuid, by, value, request, sign)
//log.debug("addChit Sql:", sql)
    db.query(sql, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("addChit row:", row)
      assert.equal(row.status, 'pend')
      done()
    })
  }
  
  const compChains = function(done) {
    let sql = 'select chit_seq, chain_idx, chain_conf, units, clean from mychips.chits_v where chit_ent = $1 order by 2'
      , rowsO, rowsS
      , dc = 2, _done = () => {
        if (!--dc) {
          assert.deepStrictEqual(rowsO, rowsS)
          done()
        }
      }
    dbO.query(sql, [userO], (e, res) => {if (e) done(e)
      rowsO = res.rows		//;log.debug('O Rows:', JSON.stringify(rowsO))
      _done()
    })
    dbS.query(sql, [userS], (e, res) => {if (e) done(e)
      rowsS = res.rows		//;log.debug('S Rows:', JSON.stringify(rowsS))
      _done()
    })
  }

  it("Foil (Subject) sends payment that doesn't arrive", function(done) {
    let dc = 2, _done = () => {if (!--dc) done()}	//dc _done's to be done
    serverS.failSend = 'success'		//Force: fail to transmit but indicate success
    addChit(dbS, 'foil', 30, userS, interTest.talS.tally_seq, _done)
    busS.register('po', (msg) => {		//log.debug("S user 3:", msg, msg.object)
      assert.equal(msg.state, 'L.good')
      assert.equal(msg.index, 3)
      _done()
    })
  })

  it("Stock (Originator) sends a payment", function(done) {
    let dc = 3, _done = () => {if (!--dc) done()}
    addChit(dbO, 'stock', 40, userO, interTest.talO.tally_seq, _done)
    busO.register('po', (msg) => {		//log.debug("O user 4:", msg, msg.object)
      assert.equal(msg.index, 3)		//at the wrong index, pre-consensus
      assert.equal(msg.state, 'L.good')
      assert.equal(msg.object?.units, 40)
      _done()
    })
    busS.register('po', (msg) => {		//log.debug("S user 4:", msg, msg.object)
      assert.equal(msg.index, 4)
      assert.equal(msg.state, 'A.good')
      assert.equal(msg.object?.units, 40)
      _done()
    })
  })

  it("Compare resulting chit chains", function(done) {
    setTimeout(c => compChains(done), 500)	//Allow consensus to settle
  })

  it("Stock (Originator) sends payment that doesn't arrive", function(done) {
    let dc = 2, _done = () => {if (!--dc) done()}	//dc _done's to be done
    serverO.failSend = 'success'		//Force: fail to transmit but indicate success
    addChit(dbO, 'stock', 60, userO, interTest.talO.tally_seq, _done)
    busO.register('po', (msg) => {		//log.debug("O user msg:", msg, msg.object)
      assert.equal(msg.state, 'L.good')
      assert.equal(msg.index, 5)
      _done()
    })
  })

  it("Foil (Subject) sends a payment", function(done) {
    let units = 50
      , dc = 3, _done = () => {if (!--dc) done()}
    addChit(dbS, 'foil', units, userS, interTest.talS.tally_seq, _done)
    busS.register('po', (msg) => {		//log.debug("S user msg:", msg, msg.object)
      if (msg.object?.units == 60) {		//Subject will get 2 messages
        assert.equal(msg.state, 'A.good')	//chit from previous test
      } else {
        assert.equal(msg.state, 'L.good')	//from this test
        assert.equal(msg.object?.units, units)
      }
      _done()
    })
    busO.register('po', (msg) => {		//log.debug("O user msg:", msg, msg.object)
      assert.equal(msg.state, 'A.good')
      assert.equal(msg.object?.units, units)
      _done()
    })
  })

  it("Compare resulting chit chains", function(done) {
    setTimeout(c => compChains(done), 500)	//Allow consensus to settle
  })

  it("Stock/foil send multiple payments that don't arrive", function(done) {
    let dc = 8, _done = () => {if (!--dc) done()}	//dc _done's to be done
    serverS.failSend = 'success'
    serverS.failCount = 2
    addChit(dbS, 'foil', 70, userS, interTest.talS.tally_seq, _done)
    addChit(dbS, 'foil', 80, userS, interTest.talS.tally_seq, _done)

    serverO.failSend = 'success'
    serverO.failCount = 2
    addChit(dbO, 'stock', 100, userO, interTest.talO.tally_seq, _done)
    addChit(dbO, 'stock', 110, userO, interTest.talO.tally_seq, _done)
    busO.register('po', (msg) => {		log.debug("O user m7:", msg, msg.object)
      assert.equal(msg.state, 'L.good')
      _done()
    })
    busS.register('po', (msg) => {		log.debug("S user m7:", msg, msg.object)
      assert.equal(msg.state, 'L.good')
      _done()
    })
  })

  it("Stock (Originator) sends a payment", function(done) {
    let dc = 3, _done = () => {if (!--dc) done()}
    addChit(dbO, 'stock', 90, userO, interTest.talO.tally_seq, _done)
    busO.register('po', (msg) => {		//log.debug("O user msg:", msg, msg.object)
      assert.equal(msg.state, 'L.good')
      _done()
    })
    busS.register('po', (msg) => {		//log.debug("S user msg:", msg, msg.object)
      assert.equal(msg.state, 'A.good')
      _done()
    })
  })

  it("Compare resulting chit chains", function(done) {
    setTimeout(c => compChains(done), 500)	//Allow consensus to settle
  })

  it("Check chain integrity using mychips.chits_v_chains", function(done) {
    let sql = 'select ok from mychips.chits_v_chains where last and ent = $1'
      , dc = 2, _done = () => {if (!--dc) {done()}}
    dbO.query(sql, [userO], (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("O row:", row)
      assert.ok(row.ok)
      _done()
    })
    dbS.query(sql, [userS], (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("S row:", row)
      assert.ok(row.ok)
      _done()
    })
  })

//  it("Mark the log files", function(done) {markLogs(dbO, log, done)})
/* */
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{		//Let things flush out before closing
      dbO.disconnect()
      dbS.disconnect()
      serverO.close()
      serverS.close()
      done()
      }, 250)
  })
}		//Suite 1

// Main
// ----------------------------------------------------------------------------
describe("Chit chain consensus", function() {
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

  describe("Test chit consensus between two users on same site", function() {Suite1(config1)})
  describe("Test chit consensus between two users on different sites", function() {Suite1(config2)})
})

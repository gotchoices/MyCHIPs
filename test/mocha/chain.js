//Test chit consensus between peers; Run only after tally, chit
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// This simulates two users connected through a single DB or two different DBs:
// User1 <-> DB <-> Agent1 <-> Agent2 <-> DB <-> User2
// User1 <-> DB1 <-> Agent1 <-> Agent2 <-> DB2 <-> User2
//TODO:
//- 
const { dbConf, testLog, Format, Bus, assert, getRow, mkUuid, dbClient } = require('./common')
var log = testLog(__filename)
const PeerCont = require("../../lib/peer2peer")
var defTally = require('./def-tally')
var defChit = require('./def-chit')
var {uSql, save, rest} = require('./def-chit')
const {host,user0,user1,user2,cid0,cid1,cid2,agent0,agent1,agent2,aCon0,aCon1,aCon2,db2Conf} = require('./def-users')
var interTest = {}			//Pass values from one test to another

var Suite1 = function({sites, dbcO, dbcS, dbcSO, dbcSS, cidO, cidS, userO, userS, agentO, agentS, aConO, aConS, saveName}) {
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

  before('Launch two peer servers', function(done) {
    serverO = new PeerCont(aConO, dbcSO)
    serverS = new PeerCont(aConS, dbcSS)
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
    let uuid = mkUuid(cidO, agentO)
      , request = 'good'
      , signed = 'Signature'
      , sql = Format(`insert into mychips.chits_v (chit_ent, chit_seq, chit_uuid, chit_type, issuer, units, request, signature)
          values (%L, %s, %L, 'tran', %L, %s, %L, %L) returning *`, ent, seq, uuid, by, value, request, signed)
//log.debug("addChit Sql:", sql)
    db.query(sql, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("addChit row:", row)
      assert.equal(row.status, 'pend')
      done()
    })
  }

  it("Foil (Subject) sends payment that doesn't arrive", function(done) {
    let dc = 2, _done = () => {if (!--dc) done()}	//dc _done's to be done
    serverS.failSend = 'success'		//Force: fail to transmit but indicate success
    addChit(dbS, 'foil', 1, userS, interTest.talS.tally_seq, _done)
    busS.register('po', (msg) => {		//log.debug("S user msg:", msg, msg.object)
      assert.equal(msg.state, 'L.good')
      delete serverS.failSend
      _done()
    })
  })

  it("Stock (Originator) sends payment", function(done) {
    let dc = 3, _done = () => {if (!--dc) done()}
dbO.query('MARK---------->')
    addChit(dbO, 'stock', 2, userO, interTest.talO.tally_seq, _done)
    busO.register('po', (msg) => {		log.debug("O user msg:", msg, msg.object)
      assert.equal(msg.state, 'L.good')
      _done()
    })
    busS.register('po', (msg) => {		//log.debug("S user msg:", msg, msg.object)
      assert.equal(msg.state, 'A.good')
      delete serverS.failSend
      _done()
    })
  })

  it("Wait for consensus to settle", function(done) {
    setTimeout(done, 250)
  })

  it("Compare resulting chit chains", function(done) {
    let sql = 'select chit_seq, chain_idx, units, clean from mychips.chits_v where chit_ent = $1 order by 2'
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

//  it("Wait for messages to settle", function(done) {
//    setTimeout(done, 250)
//  })

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
    cidO:cid0, cidS:cid1, userO:user0, userS:user1, aConO:aCon0, aConS:aCon1, agentO:agent0, agentS:agent1,
    dbcO: new dbConf(log, 'mu_p1000'), 
    dbcS: new dbConf(log, 'mu_p1001'),
    dbcSO: new dbConf(),
    dbcSS: new dbConf()
  }
  let config2 = {		//Two users on different hosts
    sites:2, saveName:'open2',
    cidO:cid0, cidS:cid2, userO:user0, userS:user2, aConO:aCon0, aConS:aCon2, agentO:agent0, agentS:agent2,
    dbcO: new dbConf(log, 'mu_p1000'), 
    dbcS: db2Conf(log, 'mu_p1002'),
    dbcSO: new dbConf(),
    dbcSS: db2Conf()
  }

  describe("Test chit consensus between two users on same site", function() {Suite1(config1)})
  describe("Test chit consensus between two users on different sites", function() {Suite1(config2)})
})

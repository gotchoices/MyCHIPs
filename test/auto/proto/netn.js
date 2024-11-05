//Build simulated network of N databases, each containing users
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- 
const Fs = require('fs')
const Path = require('path')
const { assert, testLog, Schema, dbConf, dbClient, SubCrypto, Format, Bus, getRow, peerTest, mkUuid, Stringify } = require('../common')
const {uSql, sSql} = require('./def-tally')
const log = testLog(__filename)
const crypto = new SubCrypto(log)
const contract = {domain:"mychips.org", name:"standard", version:1.0}
const clearSql = `begin;
        delete from mychips.tallies;
        delete from base.ent where ent_num >= 100;
        delete from mychips.agents;
        update mychips.users set _last_tally = 0; commit`
const agree = {domain:"mychips.org", name:"test", version:1}
const {tallyData, initSites} = require('./def-net')
var siteData = []
var userData = {}
var interTest = {}			//Pass values from one test to another

//Establish a tally between two users
const establishTally = function(dataO, dataS, units, tallyCB) {
  const dbcO = dataO.dConf, cuidO = dataO.cuid, userO = dataO.id, agentO = dataO.agent
  const dbcS = dataS.dConf, cuidS = dataS.cuid, userS = dataS.id, agentS = dataS.agent
  const busO = new Bus('busO'), busS = new Bus('busS')
  var dbO, dbS
  
  before('Connection O to ' + dbcO.dbName, function(done) {	//Emulate originator user
    dbO = new dbClient(dbcO, (chan, data) => {
      log.trace("Notify O on channel:", chan, "data:", data)
      busO.notify(JSON.parse(data))
    }, ()=>{log.info("DB O connection open: " + dbcO.listen); done()})
  })

  before('Connection S to ' + dbcS.dbName, function(done) {	//Emulate subject user
    dbS = new dbClient(dbcS, (chan, data) => {
      log.trace("Notify S on channel:", chan, "data:", data)
      busS.notify(JSON.parse(data))
    }, ()=>{log.info("DB S connection open: " + dbcS.listen); done()})
  })

  it("Originator builds draft tally and token", function(done) {
    let uuid = mkUuid(cuidO, agentO, cuidS+agentS, true)
      , s1 = Format(`insert into mychips.tallies_v (tally_ent, tally_type, tally_uuid, contract) values(%L,'foil', %L, %L)`, userO, uuid, contract)
      , sql = `with row as (${s1} returning tally_ent, tally_seq, false)
          insert into mychips.tokens (token_ent, tally_seq, reuse) select * from row returning *;
          select * from mychips.tallies_v where tally_ent = '${userO}' order by tally_seq desc limit 1;
          select token,expires,chad from mychips.tokens_v where token_ent = '${userO}' order by token_seq desc limit 1;`
//log.debug("Sql:", sql)
    dbO.query(sql, (e, res) => {if (e) done(e)		//;log.debug("res:", res)
      assert.equal(res.length, 3)
      assert.equal(res[0].rowCount, 1)
      let tok = res[0].rows[0]
      assert.equal(tok.token_ent, userO)
      assert.equal(tok.token.length, 32)	//MD5
      let tal = res[1].rows[0]			//;log.debug("Talley:", tal)
      assert.ok(!!tal.tally_uuid)
      assert.ok(!tal.part_ent)
      assert.equal(tal.status,'draft')
      assert.equal(tal.tally_type,'foil')
      assert.equal(tal.hold_cuid,cuidO)
      let ticket = res[2].rows[0]		;log.debug("Ticket:", ticket)
      interTest.tallyO = tal
      interTest.ticket = ticket
      tallyCB(tal)
      done()
    })
  })

  it("Subject asks its server to request the proposed tally", function(done) {
    let sql = Format('select mychips.ticket_process(%L,%L)', interTest.ticket, userS)
      , dc = 2, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql)
    dbS.query(sql, null, (e, res) => { if (e) done(e)
      let row = getRow(res, 0)		//;log.debug("row:", row)
      assert.ok(row.ticket_process)
      _done()
    })
    busO.register('po', (msg) => {	;log.debug("msg:", msg)
      assert.equal(msg.entity, userO)	//Originator is prompted to sign the tally
      assert.equal(msg.state, 'P.draft')
      let tally = msg.object		//,x=log.debug("tally:", tally, "S:", tally.stock, "F:", tally.foil)
        , stock = tally.stock
        , foil = tally.foil
      assert.equal(foil.cert.chad.cuid, cuidO)
      assert.equal(stock.cert.chad.cuid, cuidS)
      assert.ok(!tally.sign.stock)	//;log.debug("sign:", tally.sign)
      assert.ok(!tally.sign.foil)
      _done()
    })
  })

  it("Generate originator signature", function(done) {
    let sql = "select json_core from mychips.tallies_v where tally_ent = $1 and tally_seq = $2"
      , key = dataO.priv
    dbO.query(sql, [userO, interTest.tallyO.tally_seq], (err, res) => {
      let row = getRow(res, 0)				//;log.debug("row:", row)
        , message = Stringify(row.json_core)		//;log.debug('JSON:', message.slice(0,40))
      assert.ok(row.json_core)
      crypto.sign(key, message).then(sign => {
        let textSign = Buffer.from(sign).toString('base64url')
        assert.ok(textSign)			//;log.debug('sign:', textSign)
        interTest.sign = textSign
        done()
      })
    })
  })

  it("Originator approves, signs the proposed tally", function(done) {
    let sql = uSql('request = %L, hold_sig = %L', 'offer', interTest.sign, userO, interTest.tallyO.tally_seq)
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
      assert.equal(foil.cert.chad.cuid, cuidO)
      assert.equal(foil.cert.chad.agent, agentO)
      assert.equal(stock.cert.chad.cuid, cuidS)
      assert.equal(stock.cert.chad.agent, agentS)
      assert.ok(!tally.sign.stock)		//;log.debug("sign:", tally.sign)
      assert.ok(!!tally.sign.foil)
      assert.ok(!tally.part_ent)		//Haven't linked partner yet
      interTest.msgS = msg
      interTest.tallyS = tally
      _done()
    })
    busO.register('po', (msg) => {		//;log.debug("O msg:", msg, msg.object.sign)
      assert.equal(msg.entity, userO)		//Originator is sent the close request
      assert.equal(msg.state, 'H.offer')
      assert.ok(!msg.object.sign.stock)
      assert.ok(!!msg.object.sign.foil)
      _done()
    })
  })

  it("Generate subject signature", function(done) {
    let sql = "select json_core from mychips.tallies_v where tally_ent = $1 and tally_seq = $2"
      , key = dataS.priv
    dbS.query(sql, [userS, interTest.msgS.sequence], (err, res) => {
      let row = getRow(res, 0)				//;log.debug("row:", row)
        , message = Stringify(row.json_core)		//;log.debug('JSON:', message.slice(0,40))
      assert.ok(row.json_core)
      crypto.sign(key, message).then(sign => {
        let textSign = Buffer.from(sign).toString('base64url')
        assert.ok(textSign)			//;log.debug('sign:', textSign)
        interTest.sign = textSign
        done()
      })
    })
  })

  it("Subject accepts the proposed tally", function(done) {
    let seq = interTest.msgS.sequence
      , sql = uSql('request = %L, hold_sig = %L', 'open', interTest.sign, userS, seq)
      , dc = 3, _done = () => {if (!--dc) done()}
//log.debug("Sql:", sql)
    dbS.query(sql, (err, res) => { if (err) done(err)
      let row = getRow(res, 0)			//;log.debug("row:", row)
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

  it("Create chit signature independant of DB", function(done) {
    let type = 'tran'
      , by = 'foil'
      , ref = {payee: cuidS}
      , memo = 'Pay: ' + units
      , uuid = mkUuid(cuidO, agentO, memo, true)
      , tally = interTest.tallyO.tally_uuid
      , date = new Date().toISOString()
      , key = dataO.priv
      , core = {by, date, memo, ref, tally, type, uuid, units}	//;log.debug("c:", core)
    crypto.sign(key, core).then(sign => {
      let text = Buffer.from(sign).toString('base64url')
      assert.ok(text)			//;log.debug('sign:', text)
      interTest.sign = {key, sign, text, core}
      done()
    })
  })

  it("Originator sends payment to Subject", function(done) {
    let {sign, text, core} = interTest.sign
      , { by, date, memo, ref, tally, type, uuid, units } = core
      , seq = interTest.tallyO.tally_seq
      , request = 'good'
      , sql = Format(`insert into mychips.chits_v (chit_ent, chit_seq, chit_uuid, chit_date, chit_type, issuer, units, reference, memo, request, signature)
          values (%L, %s, %L, %L, 'tran', %L, %s, %L, %L, %L, %L) returning *`, userO, seq, uuid, date, by, units, ref, memo, request, text)
      , dc = 3, _done = () => {if (!--dc) done()}	//dc _done's to be done
//log.debug("Sql:", sql)
    dbO.query(sql, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.chit_ent, userO)
      assert.equal(row.chit_uuid, uuid)
      assert.equal(row.units, units)
      assert.equal(row.net, -units)
      assert.equal(row.request, request)
      assert.deepStrictEqual(row.reference, ref)
      _done()
    })
    busS.register('ps', (msg) => {		//log.debug("S user msg:", msg, msg.object)
      assert.equal(msg.state, 'A.good')
      let obj = msg.object
      assert.deepStrictEqual(obj.ref, ref)
      assert.equal(obj.units, units)
      assert.equal(obj.uuid, uuid)
      assert.ok(obj.sign)
      _done()
    })
    busO.register('po', (msg) => {		//log.debug("O user msg:", msg, msg.object)
      assert.equal(msg.state, 'L.good')
      _done()
    })
  })

/* */
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{		//Let everything flush out before closing
      dbO.disconnect()
      dbS.disconnect()
      done()
      }, 200)
  })
}	//Establish Tally

describe("Create simulated network", function() {
  this.timeout(20000)
  initSites(log, siteData, userData)

  siteData.forEach(s => {  
    it('Connect to database ' + s.dbName, function(done) {
      s.db = new dbClient(s.dConf, null, () => {
        log.info("DB connection established:" + s.dbName)
        done()
      })
    })
    it("Clear existing data in DB " + s.idx, function(done) {
      s.db.query(clearSql, (e) => {if (e) done(e)
        done()
      })
    })
    it("Launch peer server on " + s.idx, function(done) {
      s.ps = new peerTest(s.aConf, s.dConf)
      done()
    })
  })

  Object.values(userData).forEach(u => {	//log.debug('User:', u)
    let sql = `insert into mychips.users_v 
        (ent_type, ent_num, ent_name, peer_cuid, peer_agent, peer_host, peer_port, user_cmt, user_psig)
        values ($1, $2, $3, $4, $5, $6, $7, $8, $9) returning *;`
      , { agent, aConf } = u.site
//      , private = JSON.stringify(u.private)

    it("Build user: " + u.id + " on site " + u.site.idx, function(done) {
      crypto.generate().then(({keys, priv, publ}) => {
        let parms = [u.type, u.num, u.name, u.cuid, u.agent, aConf.host, aConf.port, priv, publ]
        Object.assign(u, {priv, publ})			//;log.debug('Sql:', sql, parms)
        u.site.db.query(sql, parms, (e, res) => {if (e) done(e)
          assert.equal(res.rowCount, 1)
          let row = res.rows[0]				//;log.debug('row:', row)
          assert.equal(row.id, u.id)
          assert.equal(row.peer_cuid, u.cuid)
          assert.equal(row.peer_agent, u.agent)
//        assert.equal(row.user_cmt, u.priv)
          done()
        })
      })
    })
  })

  tallyData.forEach((t,idx) => {		//log.debug('Tally:', idx, t)
    let [ orig, subj, units ] = t
    describe("Establish tally between " + orig + " and " + subj, function() {
      establishTally(userData[orig], userData[subj], units, tal => {
        tallyData[idx].uuid = tal.tally_uuid		//;log.debug('T-post:', tal.tally_uuid)
      })
    })
  })

  after("Build visualization graph", function(done) {
    let top = `@startdot\ndigraph testNet {\n  label = "Test Network"\n`
      , bot = `}\n@enddot\n`
      , file = Path.join(__dirname, '..', 'data', 'testNet.puml')
      , text = ''
    siteData.forEach(s => {  			//log.debug("S:", s.idx, s)
      let truncAgent = s.agent.slice(0,3) + '..' + s.agent.slice(-3)
      let t = `  subgraph cluster_${s.idx} {\n    label = "Site: ${s.idx}, Agent: ${truncAgent}"\n`
      Object.values(userData).forEach(u => {	//log.debug("U-check:", u.cuid, u.site.idx)
        if (u.site.idx == s.idx) {
          t += `    ${u.cuid} [label="${u.id}\\n${u.cuid}"];\n`
        }
      })
      text += t + `\n  }\n\n`
    })
    tallyData.forEach(t => {
      let [orig, subj, units, format ] = t
        , cuidO = userData[orig].cuid, cuidS = userData[subj].cuid
        , truncUuid = t?.uuid?.slice(-4)	//;log.debug('T:', t, t.uuid)
      text += `  ${cuidO} -> ${cuidS} [label="${truncUuid}\n${units}"${format ? ','+format: ''}]\n`
    })
    text += `\n`
    
    Fs.writeFile(file, top + text + bot, done)
  })

/* */
  after('Disconnect from test databases', function(done) {
    siteData.forEach(s => {  
      s.db.disconnect()
      s.ps.close()
    })
    done()
  })
})

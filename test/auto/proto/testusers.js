//Setup sample users for tests; run
//After: ../schema/dbinit
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- 
const { DBName, Schema, dbConf, testLog, Format, Bus, assert, dbClient, SubCrypto, pgCheck, Data, importCheck, dropDB } = require('../common')
var log = testLog(__filename)
var crypto = new SubCrypto(log)
var { host, user0, user1, port0, port1, agent0, agent1, aCon0, aCon1, cuid0, cuid1 } = require('../def-users')
var interTest = {}

describe("Establish test users", function() {
  var db

  before('PostgreSQL check', function() {
    return pgCheck(this)
  })

  before('Connection to database', function(done) {
    this.timeout(10000)		//May take a while to build database
    db = new dbClient(new dbConf(log,undefined,undefined,Schema), () => {}, done)
  })

  it('Delete any test users', function(done) {
    db.query("delete from base.ent where ent_num >= $1;", [100] ,(err, res) => {done()})
  })

  it("Import multiple entities", function(done) {
    let file = Data('users.json')
    importCheck(file, null, db, done, function(res, row) {
log.debug('res:', res, 'row:', row)
      assert.equal(row[0],'p1002'); 
      done()
    })
  })

  it('Delete org user', function(done) {
    db.query("delete from base.ent where ent_type = $1;", ['o'] ,(err, res) => {done()})
  })

  it("Build User Keys", function(done) {
    let dc = 2, _done = () => {if (!--dc) done()}	//dc _done's to be done
    crypto.generate().then(({keys, priv, publ}) => {
      assert.ok(keys?.publicKey)
      assert.ok(keys?.privateKey)
      assert.ok(publ?.x)
      assert.ok(publ?.y)
      interTest.uKey0 = publ
      interTest.rKey0 = JSON.stringify(priv)		//Stash private key in user's comment
      _done()
    })
    crypto.generate().then(({keys, priv, publ}) => {	//log.debug('key1:', publ)
      interTest.uKey1 = publ
      interTest.rKey1 = JSON.stringify(priv)
      _done()
    })
  })

  it("Initialize test users", function(done) {
    let fields = 'peer_host = %L, peer_port=%L, peer_agent=%L, user_psig=%L, user_cmt=%L'
      , f0 = Format(fields, host, port0, agent0, interTest.uKey0, interTest.rKey0)
      , f1 = Format(fields, host, port1, agent1, interTest.uKey1, interTest.rKey1)
      , sql = `begin;
        delete from base.ent where ent_num > 1001;
        delete from mychips.tallies;
        update mychips.users set _last_tally = 0;
        update mychips.users_v set ${f0} where user_ent = '${user0}';
        update mychips.users_v set ${f1} where user_ent = '${user1}';
        select count(*) as count from mychips.users_v where ent_num >= 1000; commit;`
//log.debug("Sql:", sql)
    db.query(sql, (err, res) => {if (err) done(err)
      assert.equal(res.length, 8)	//8: begin, del, del, upd, upd, upd, select, commit
//log.debug("Res:", res[6].rows[0])
      let row = res[6].rows[0]
log.info("Users:", row.count)
      assert.equal(row.count,2)
      done()
    })
  })
/* */
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{
      db.disconnect()
      }, 200)
    done()
  })
});

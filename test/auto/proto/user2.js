//Setup a sample user on a separate db; Run
//After: testusers
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- 
const { DB2Name, dbConf, DBAdmin, Schema, testLog, Format, Bus, assert, importCheck, dropDB, dbClient, develop, SubCrypto, Data } = require('../common')
var log = testLog(__filename)
var crypto = new SubCrypto(log)
var { host, user2, port2, agent2, aCon2, cuid2, db2Conf } = require('../def-users')
var schema = Schema
var interTest = {}

describe("Establish test user on separate DB", function() {
  var db

  before('Delete test database', function(done) {dropDB(done, DB2Name)})

  before('Connection to database', function(done) {
    this.timeout(10000)		//May take a while to build database
    db = new dbClient(db2Conf(), () => {}, ()=>{done()})
  })

  it('Build development DB objects', function(done) {
    this.timeout(5000)
    develop(db, done)
  })

  it("Create dummy users users for padding user IDs", function(done) {
    let fields = '(ent_name, peer_cuid) values (%L,%L)'
      , f0 = Format(fields, 'A', 'a')
      , f1 = Format(fields, 'B', 'b')
      , sql = `begin; insert into mychips.users_v ${f0}; insert into mychips.users_v ${f1}; commit`
//log.debug("Sql:", sql)
    db.query(sql, (err, res) => {if (err) done(err); done()})
  })

  it("Import self-identifying user record", function(done) {
    let file = Data('something.json')
    importCheck(file, null, db, done, function(res, row) {
      assert.equal(row[0],user2); done()
    })
  })

  it("Build User Key", function(done) {
    crypto.generate().then(({keys, priv, publ}) => {	//log.debug('key1:', publ)
      interTest.uKey2 = publ
      interTest.rKey2 = JSON.stringify(priv)		//Stash private key in user's comment
      done()
    })
  })
  
  it("Initialize test user on db 2", function(done) {
    let fields = 'peer_host = %L, peer_port=%L, peer_agent=%L, user_psig=%L, user_cmt=%L'
      , f1 = Format(fields, host, port2, agent2, interTest.uKey2, interTest.rKey2)
      , sql = `begin;
        delete from base.ent where ent_num > 1002;
        delete from mychips.tallies;
        update mychips.users set _last_tally = 0;
        update mychips.users_v set ${f1} where user_ent = '${user2}';
        select count(*) as count from mychips.users_v where ent_num >= 1000; commit;`
//log.debug("Sql:", sql)
    db.query(sql, (err, res) => {if (err) done(err)
      assert.equal(res.length, 7)	//8: begin, del, del, upd, upd, select, commit
//log.debug("Res:", res[5].rows[0])
      let row = res[5].rows[0]
//log.info("Users:", row.count)
      assert.equal(row.count,3)
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

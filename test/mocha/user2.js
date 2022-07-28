//Setup a sample user on a separate db; Run before 2-db tally tests
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- 
const Path = require('path')
const { DB2Name, dbConf, DBAdmin, Schema, testLog, Format, Bus, assert, importCheck, dropDB, dbClient } = require('./common')
var log = testLog(__filename)
var { host, user2, uKey2, port2, agent2, aCon2, cid2, db2Conf } = require('./def-users')
var schema = Schema

describe("Establish test user on separate DB", function() {
  var db

  before('Delete test database', function(done) {dropDB(done, DB2Name)})

  before('Connection to database', function(done) {
    this.timeout(10000)		//May take a while to build database
    db = new dbClient(db2Conf(), () => {}, ()=>{done()})
  })

  it("Create dummy users users for padding user IDs", function(done) {
    let fields = '(ent_name, peer_cid) values (%L,%L)'
      , f0 = Format(fields, 'A', 'a')
      , f1 = Format(fields, 'B', 'b')
      , sql = `begin; insert into mychips.users_v ${f0}; insert into mychips.users_v ${f1}; commit`
//log.debug("Sql:", sql)
    db.query(sql, (err, res) => {if (err) done(err); done()})
  })

  it("Import self-identifying user record", function(done) {
    let file = Path.join(__dirname, 'something.json')
    importCheck(file, null, db, done, function(res, row) {
      assert.equal(row[0],user2); done()
    })
  })

  it("Initialize test user on db 2", function(done) {
    let fields = 'peer_host = %L, peer_port=%L, peer_agent=%L, peer_psig=%L'
      , f1 = Format(fields, host, port2, agent2, uKey2)
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

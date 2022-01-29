//Setup sample users for tests; Run after impexp and before tally tests
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- 
const { dbConf, Log, Format, Bus, assert } = require('../settings')
var log = Log('testUsers')
var { dbClient } = require("wyseman")
const Port0=65434
const Port1=65435
const user0 = 'p1000'
const user1 = 'p1001'
var host = 'localhost'
var aKey0 = Buffer.from('P'+Port0).toString('base64url')
var aKey1 = Buffer.from('Q'+Port1).toString('base64url')
var uKey0 = Buffer.from('X'+user0).toString('base64url')
var uKey1 = Buffer.from('Y'+user1).toString('base64url')
var agent0 = {host, port: Port0, key:{publicKey:aKey0}}
var agent1 = {host, port: Port1, key:{publicKey:aKey1}}

module.exports = {host, user0, user1, Port0, Port1, uKey0, uKey1, aKey0, aKey1, agent0, agent1}

describe("Establish test users", function() {
  var db

  before('Connection to database', function(done) {
    db = new dbClient(new dbConf(), () => {}, ()=>{done()})
  })

  it("Initialize test users", function(done) {
//log.debug("Key:", agent0.key.publicKey)
    let fields = 'peer_host = %L, peer_port=%L, peer_agent=%L, peer_psig=%L'
      , f0 = Format(fields, host, Port0, aKey0, uKey0)
      , f1 = Format(fields, host, Port1, aKey1, uKey1)
      , sql = `begin;
        delete from base.ent where ent_num > 1001;
        delete from mychips.tallies;
        update mychips.users set _last_tally = 0;
        update mychips.users_v set ${f0} where peer_ent = 'p1000';
        update mychips.users_v set ${f1} where peer_ent = 'p1001';
        select count(*) as count from mychips.users_v where ent_num >= 1000; commit;`
log.debug("Sql:", sql)
    db.query(sql, (err, res) => {if (err) done(err)
      assert.equal(res.length, 8)	//8: begin, del, del, upd, upd, upd, select, commit
//log.debug("Res:", res[6].rows[0])
      let row = res[6].rows[0]
log.info("Users:", row.count)
      assert.equal(row.count,2)
      done()
    })
  })

  after('Disconnect from test database', function(done) {
    setTimeout(()=>{
      db.disconnect()
      }, 200)
    done()
  })
});

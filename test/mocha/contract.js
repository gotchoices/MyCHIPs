//Check for valid contracts in database
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- 
const assert = require("assert");
const { DBName, DBAdmin, testLog, Schema, SchemaDir, dbClient, develop } = require('./common')
var log = testLog(__filename)
const dbConfig = {database:DBName, user:DBAdmin, connect:true, log, schema:Schema}

describe("Tally contract checks", function() {
  var db

  before('Connect to (or create) test database', function(done) {
    this.timeout(10000)		//May take a while to build database
    db = new dbClient(dbConfig, (chan, data) => {}, done)
  })

  it('Find expected number of contracts', function(done) {
    let sql = `select count(*) from mychips.contracts_v`
log.debug("Sql:", sql)
    db.query(sql, (e, res) => {if (e) done(e)
log.debug("res:", res)
      assert.equal(res?.rows?.length, 1)
      assert.equal(res?.rows?.[0].count, 12)
      done()
    })
  })

  it('Find contracts with bad hash', function(done) {
    let sql = `select * from mychips.contracts_v where not clean`
log.debug("Sql:", sql)
    db.query(sql, (e, res) => {if (e) done(e)
log.debug("res:", res)
      assert.equal(res.rows.length, 0)
      done()
    })
  })

/* */
  after('Disconnect from test database', function() {
    db.disconnect()
  })
});

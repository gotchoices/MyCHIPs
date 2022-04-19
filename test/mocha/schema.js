//General schema tests
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO
//- 
const assert = require("assert");
const { DBName, DBAdmin, testLog, Schema, dbClient } = require('./common')
var log = testLog(__filename)
const dbConfig = {database:DBName, user:DBAdmin, connect:true, log, schema:Schema}
const SchemaList = "'mychips','json'"

describe("General schema tests", function() {
  var db
  
  before('Connect to (or create) test database', function(done) {
    this.timeout(4000)		//May take a while to build database
    db = new dbClient(dbConfig, (chan, data) => {}, done)
  })

  it('Check for undocumented tables', function(done) {
    let sql = `select sch,tab from wm.table_lang where help is null and sch in (${SchemaList}) order by 1,2`
log.debug("Sql:", sql)
    db.query(sql, (e, res) => {if (e) done(e)
//log.debug("res:", res.rows ? JSON.stringify(res.rows) : null)
      assert.equal(res.rows.length, 0)
      done()
    })
  })

  it('Check for undocumented columns', function(done) {
    let sql = `select sch,tab,col from wm.column_lang where help is null and sch in (${SchemaList}) order by 1,2`
log.debug("Sql:", sql)
    db.query(sql, (e, res) => {if (e) done(e)
//log.debug("res:", res)
      assert.equal(res.rows.length, 0)
      done()
    })
  })
/* */
  after('Disconnect from test database', function(done) {
    db.disconnect()
    done()
  })
})

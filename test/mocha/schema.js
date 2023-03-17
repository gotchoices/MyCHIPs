//General schema tests, also instantiate development schema objects
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- 
const Fs = require('fs')
const assert = require("assert");
const { DBName, DBAdmin, testLog, Schema, SchemaDir, dbClient, develop } = require('./common')
var log = testLog(__filename)
const dbConfig = {database:DBName, user:DBAdmin, connect:true, log, schema:Schema}

describe("General schema checks", function() {
  var db

  before('Connect to (or create) test database', function(done) {
    this.timeout(10000)		//May take a while to build database
    db = new dbClient(dbConfig, (chan, data) => {}, done)
  })

  it('Build development schema objects ("make run" in schema dir to undo)', function(done) {
    this.timeout(5000)
    develop(DBName, done)
  })

  it('find columns with ambiguous inheritance', function(done) {
    let sql = `select * from wm.column_ambig where not spec`
log.debug("Sql:", sql)
    db.query(sql, (e, res) => {if (e) done(e)
//log.debug("res:", res)
      assert.equal(res.rows.length, 0)
      done()
    })
  })

/* */
  after('Disconnect from test database', function() {
    db.disconnect()
  })
});

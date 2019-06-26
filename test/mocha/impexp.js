//Test json import and export functions
//TODO:
//- 

const assert = require("assert");
const { DatabaseName, DBAdmin, Log } = require('../settings')
var fs = require('fs')
var log = Log('testImpexp')
var { dbClient } = require("wyseman")
const dbConfig = {
  database: DatabaseName,
  user: DBAdmin,
  listen: "DummyChannel",		//Cause immediate connection to DB, rather than deferred
  logger: log,
  schema: __dirname + "/../../lib/schema.sql"
}

function dbAndCheck(sqlFile, db, done, check) {
  fs.readFile(sqlFile, (err, fileData) => {
    if (err) done(err)
    var jsonData = JSON.parse(fileData)
    db.query("select json.import($1::jsonb) as record;", [jsonData] ,(err, res) => {
      if (err) done(err)
      log.debug("Result:", res.rows[0].record)
      check(res,res.rows[0].record.slice(1,-1).split(','))
    })
  })
}

describe("JSON import/export", function() {
  var db

  before('Connect to (or create) test database', function(done) {
    db = new dbClient(dbConfig, (chan, data) => {
      log.trace("Notify from channel:", chan, "data:", data)
    }, ()=>{log.trace("Connected"); done()})
  })

  before('Delete all test users if there are any', function(done) {
    db.query("delete from base.ent where ent_num >= $1;", [100] ,(err, res) => {done()})
  })

  it("Import Chips test organization", function(done) {
    dbAndCheck(__dirname + "/../sample/org.json", db, done, function(res, row) {
      assert.equal(row[0],'o500'); done()
    })
  })

  it("Import user 1", function(done) {
    dbAndCheck(__dirname + "/../sample/user1.json", db, done, function(res, row) {
      assert.equal(row[0],'p1000'); done()
    })
  })
  it("Import user 2", function(done) {
    dbAndCheck(__dirname + "/../sample/user2.json", db, done, function(res, row) {
      assert.equal(row[0],'p1001'); done()
    })
  })

  after('Disconnect from test database', function(done) {
console.log("After:")
    db.disconnect()
    done()
  })
});

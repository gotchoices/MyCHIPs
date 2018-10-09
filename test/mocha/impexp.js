//Test json import and export functions
//TODO:
//- 

const assert = require("assert");
const DatabaseName = "kyle"			//"mychipsTestDB"
var fs = require('fs')
var log = require('../../lib/logger')('testImpex')
var { dbClient } = require("wyseman")
const dbConfig = {
  database: DatabaseName,
  listen: "DummyChannel",		//Cause immediate connection to DB, rather than deferred
  logger: log,
  schema: __dirname + "/../../lib/schema.sql"
}

describe("JSON import/export", function() {
  var db

  before('Connect to (or create) test catabase', function(done) {
    db = new dbClient(dbConfig, (chan, data) => {
      log.trace("Notify from channel:", chan, "data:", data)
    }, ()=>{
      log.trace("Connected")
      done()
    })
  })

  it("Import", function(done) {
    fs.readFile(__dirname + "/../sample/org.json", (err, fileData) => {
      if (err) throw err;
      var jsonData = JSON.parse(fileData)
//      var jsonData = JSON.parse('{"user":1234}')
console.log("JSON:", jsonData)
      db.query("select json.import($1::jsonb);", [jsonData] ,(err, res) => {
console.log("Err:", err, "Res:", res)
        assert.equal(true,true)
        done()
      })
    })
  })

  after('Disconnect from test database', function(done) {
//    server2.close(serv1)
    db.disconnect
    done()
  })
});

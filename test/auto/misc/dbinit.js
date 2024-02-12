//Initialize the database
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- 
const assert = require("assert");
const { dbConf, testLog, Schema, DBName, dropDB, dbClient, develop, pgCheck } = require('../common')
var log = testLog(__filename)

describe("Start with blank database", function() {
  var db
  before('PostgreSQL check', function() {
    this.timeout(10000)
    return pgCheck()
  })
  
  before('Delete test database', function(done) {dropDB(done)})

  before('Connect to (or create) test database', function(done) {
    this.timeout(10000)		//May take a while to build database
    db = new dbClient(new dbConf(log,undefined,undefined,Schema), (chan, data) => {}, done)
  })

  it("Build development objects", function(done) {
    this.timeout(5000)
    develop(db, done)
  })
  
  after('Disconnect from test database', function() {
    db.disconnect()
  })
})

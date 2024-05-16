//Initialize the database
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- 
const assert = require("assert");
const { dbConf, testLog, Schema, DBName, dropDB, dbClient, develop, pgCheck } = require('../common')
var log = testLog(__filename)

describe("Start with blank database", function() {
  this.timeout(20000)
  var db

  before('PostgreSQL check', function() {
    return pgCheck(this)
  })
  
  before('Delete test database', function(done) {
    dropDB(done);
  })

  before('Connect to (or create) test database', function(done) {
    db = new dbClient(new dbConf(log,undefined,undefined,Schema), (chan, data) => {}, done)
  })

  it('Build development schema objects ("make run" in schema dir to undo)', function(done) {
    develop(db, done)
  })
  
  after('Disconnect from test database', function() {
    db.disconnect()
  })
})

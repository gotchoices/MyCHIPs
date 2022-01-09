//Test json import and export functions
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- 

const Child = require('child_process')
const Path = require('path')
const assert = require("assert");
const { Database, DBAdmin, Log, Schema } = require('../settings')
const fs = require('fs')
var log = Log('testImpexp')
var { dbClient } = require("wyseman")
const dbConfig = {database:Database, user:DBAdmin, connect:true, log, schema:Schema}

function dbAndCheck(fileName, target, db, done, check) {
  fs.readFile(fileName, (err, fileData) => {
    if (err) done(err)
    var jsonData = JSON.parse(fileData)
    db.query("select json.import($1::jsonb, $2::text) as record;", [jsonData, target] ,(err, res) => {
      if (err) done(err)
      log.debug("Result:", res.rows[0].record)
      check(res,res.rows[0].record.slice(1,-1).split(','))
    })
  })
}

describe("JSON import/export", function() {
  var db
  this.timeout(5000)		//May take a while to build database

  before('Delete test database', function(done) {
    Child.exec(`dropdb -U ${DBAdmin} ${Database}`, done)
  })

  before('Connect to (or create) test database', function(done) {
    db = new dbClient(dbConfig, (chan, data) => {}, done)
  })

  before('Delete all test users if there are any', function(done) {
    db.query("delete from base.ent where ent_num >= $1;", [100] ,(err, res) => {done()})
  })

  it("Import known user record", function(done) {
    let file = Path.join(__dirname, 'user.json')
    dbAndCheck(file, 'user', db, done, function(res, row) {
      assert.equal(row[0],'p1000'); done()
    })
  })
  it("Import self-identifying user record", function(done) {
    let file = Path.join(__dirname, 'something.json')
    dbAndCheck(file, null, db, done, function(res, row) {
      assert.equal(row[0],'p1001'); done()
    })
  })

  it('Delete test users again', function(done) {
    db.query("delete from base.ent where ent_num >= $1;", [100] ,(err, res) => {done()})
  })

  it("Import multiple entities", function(done) {
    let file = Path.join(__dirname, 'users.json')
    dbAndCheck(file, null, db, done, function(res, row) {
//console.log('res:', res, 'row:', row)
      assert.equal(row[0],'p1002'); 
      done()
    })
  })

  after('Disconnect from test database', function() {
    db.disconnect()
  })
});

//Test json import and export functions
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- 

const Child = require('child_process')
const Fs = require('fs')
const Path = require('path')
const Stringify = require('json-stable-stringify')	//Predictable property order
const assert = require("assert");
const { Database, DBAdmin, Log, Schema, importCheck } = require('../settings')
var log = Log('testImpexp')
var { dbClient } = require("wyseman")
const dbConfig = {database:Database, user:DBAdmin, connect:true, log, schema:Schema}

describe("JSON contact import/export", function() {
  var db
  this.timeout(5000)		//May take a while to build database

  before('Delete test database', function(done) {
    Child.exec(`dropdb --if-exists -U ${DBAdmin} ${Database}`, done)
  })

  before('Connect to (or create) test database', function(done) {
    db = new dbClient(dbConfig, (chan, data) => {}, done)
  })

  before('Delete all test users if there are any', function(done) {
    db.query("delete from base.ent where ent_num >= $1;", [100] ,(err, res) => {done()})
  })

  it("Import known user record", function(done) {
    let file = Path.join(__dirname, 'user.json')
    importCheck(file, 'user', db, done, function(res, row) {
      assert.equal(row[0],'p1000'); done()
    })
  })
  it("Import self-identifying user record", function(done) {
    let file = Path.join(__dirname, 'something.json')
    importCheck(file, null, db, done, function(res, row) {
      assert.equal(row[0],'p1001'); done()
    })
  })

  it('Delete test users again', function(done) {
    db.query("delete from base.ent where ent_num >= $1;", [100] ,(err, res) => {done()})
  })

  it("Import multiple entities", function(done) {
    let file = Path.join(__dirname, 'users.json')
    importCheck(file, null, db, done, function(res, row) {
log.debug('res:', res, 'row:', row)
      assert.equal(row[0],'p1002'); 
      done()
    })
  })

  after('Disconnect from test database', function() {
    db.disconnect()
  })
});

describe("JSON certificate import/export", function() {
  var db

  before('Connect to (or create) test database', function(done) {
    db = new dbClient(dbConfig, (chan, data) => {}, done)
  })

  it("Import user certificate", function(done) {
    let file = Path.join(__dirname, 'cert.json')
    importCheck(file, null, db, done, function(res, row) {
log.debug("Row:", row)
      assert.equal(row[0],'p1003')
      done()
    })
  })

  it("Export certificate and compare to original", function(done) {
    let file = Path.join(__dirname, 'cert.json')
      , fileData = Fs.readFileSync(file)
      , fileObj = JSON.parse(fileData).cert
    delete fileObj.date
    let fileStr = Stringify(fileObj)
      , sql = "select to_json(s) as cert from (select * from json.cert where id = $1) s"
    db.query(sql, ['p1003'] ,(err, res) => {if (err) done(err)
      assert.equal(res.rowCount, 1)
      let cert = res.rows[0].cert
      delete cert.date		//Date won't be the same
      delete cert.id		//Auto-generated id in the DB
      let certStr = Stringify(cert)
log.debug("Cert:", cert)
      assert.equal(certStr, fileStr)
      done()
    })
  })

  after('Disconnect from test database', function() {
    db.disconnect()
  })
});

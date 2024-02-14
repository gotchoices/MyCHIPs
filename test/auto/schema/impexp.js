//Test json import and export functions; run
//After: dbinit
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- 
const Fs = require('fs')
const Stringify = require('json-stable-stringify')	//Predictable property order
const assert = require("assert");
const { dbConf, testLog, importCheck, dbClient, pgCheck, Data } = require('../common')
var log = testLog(__filename)

describe("JSON contact import/export", function() {
  var db
  before('PostgreSQL check', function() {
    return pgCheck(this)
  })
  
  before('Connect to test database', function(done) {
    db = new dbClient(new dbConf(), (chan, data) => {}, done)
  })

  before('Delete any test users', function(done) {
    db.query("delete from base.ent where ent_num >= $1;", [100] ,(err, res) => {done()})
  })

  it("Import known user record", function(done) {
    let file = Data('user.json')	//;log.debug('file:', file)
    importCheck(file, 'user', db, done, function(res, row) {
      assert.equal(row[0],'p1000'); done()
    })
  })
  it("Import self-identifying user record", function(done) {
    let file = Data('something.json')
    importCheck(file, null, db, done, function(res, row) {
      assert.equal(row[0],'p1001'); done()
    })
  })

  it('Delete test users again', function(done) {
    db.query("delete from base.ent where ent_num >= $1;", [100] ,(err, res) => {done()})
  })

  it("Import multiple entities", function(done) {
    let file = Data('users.json')
    importCheck(file, null, db, done, function(res, row) {
//log.debug('res:', res, 'row:', row)
      assert.equal(row[0],'p1002'); 
      done()
    })
  })

/* */
  after('Disconnect from test database', function() {
    db.disconnect()
  })
});

describe("JSON certificate import/export", function() {
  var db

  before('Connect to test database', function(done) {
    db = new dbClient(new dbConf(), (chan, data) => {}, done)
  })

  it("Import user certificate", function(done) {
    let file = Data('cert.json')
    importCheck(file, null, db, done, function(res, row) {
//log.debug("Row:", row)
      assert.equal(row[0],'p1003')
      done()
    })
  })

  it("Export certificate and compare to original", function(done) {
    let file = Data('cert.json')
      , fileData = Fs.readFileSync(file)
      , fileObj = JSON.parse(fileData).cert
    delete fileObj.date
    let fileStr = Stringify(fileObj)
      , sql = "select json_strip_nulls(to_json(s)) as cert from (select * from json.cert where id = $1) s"
    db.query(sql, ['p1003'] ,(err, res) => {if (err) done(err)
      assert.equal(res.rowCount, 1)
      let cert = res.rows[0].cert
      delete cert.date		//Date won't be the same
      delete cert.id		//Auto-generated id in the DB
      let certStr = Stringify(cert)
//log.debug("Cert:", cert)
      assert.equal(certStr, fileStr)
      done()
    })
  })

  it("Import tally", function(done) {
    let file = Data('tally.json')
    importCheck(file, 'tally', db, done, function(res, row) {
      assert.equal(row[0],'p1000')
      done()
    })
  })
/* */
  after('Disconnect from test database', function() {
    db.disconnect()
  })
});

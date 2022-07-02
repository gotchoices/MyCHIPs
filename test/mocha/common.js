//Shared routines/values for regression tests
// -----------------------------------------------------------------------------
// TODO:
//- cleanupPG fails to stop docker if docker was already running (is this OK?)
//- 
const Fs = require('fs')
const Path = require('path')
const Net = require('net')
const Child = require('child_process')
const Format = require('pg-format')
const Uuid = require('uuid')
const assert = require('assert');
const Bus = require('../bus')
const DBName = "mychipsTestDB"
const dockName = 'mychipsTestPG'
const { DBHost, DBPort, DBAdmin, Log } = require('../settings.js')
const { dbClient } = require("wyseman")
var dockerPgDown = null		//command to kill docker postgres

var testLog = function(fname) {		//Initiate a logging service for a mocha test file
    let base = Path.parse(fname).name
      , logName = fname ? 'test-' + base : 'combined.log'
    return Log(logName)
  }
var log = testLog(__filename)

module.exports={
  DBName,
  DB2Name: DBName + '2',
  DBAdmin, DBHost, DBPort, Log, dbClient,
  Format, assert, Bus, testLog,
  Schema: Path.join(__dirname, '../..', 'lib', 'schema.json'),
  dbConf: function(log, listen, database = DBName, schema) {
    Object.assign(this, {database, user: DBAdmin, connect: true, log, listen, schema})
  },

  checkPG: function(done) {		//Make sure we have a Postgres running
    let sock = Net.connect(DBPort, DBHost, () => {
log.debug("Found Postgres at:", DBHost, DBPort)
      sock.end()
      done()
    })
    sock.on('error', e => {		//Can't connect to postgres
//log.debug("checkPG error:", e)
      if (e.code != 'ECONNREFUSED') throw(e)
      let buildDir = Path.join(__dirname, '../..', 'build')
        , compFile = Path.join(buildDir, 'compose-pg.yml')
        , cmd = `docker-compose -p pg -f ${compFile}`
        , env = Object.assign({MYCHIPS_DBHOST: dockName}, process.env)
log.debug("Launching docker with compose:", cmd)
      Child.exec(cmd + ' up -d', {env}, (e,out,err) => {	//Try to launch one in docker
//log.debug("Compose result:", e)
        if (e && e.code == 127) throw "Can't find running postgres or docker-compose environment"
        if (!e) dockerPgDown = cmd + ' down'
        done()
      })
    })
  },

  cleanupPG: function(done) {			//Take down docker postgres
//log.debug("Docker down command:", dockerPgDown)
    if (dockerPgDown) Child.exec(dockerPgDown, (err, out) => {
log.debug("Taking down docker PG")
      dockerPgDown = null
      done()
    })
    else done()
  },

  dropDB: function(done, dbName = DBName) {	//Destroy the test database
    let config = {database:'template1', user: DBAdmin, connect: true}
      , sql = Format('drop database if exists "%s";', dbName)
      , db = new dbClient(config, (chan, data) => {}, () => {
      db.query(sql, (e, res) => {if (e) done(e)
        db.disconnect()
        setTimeout(done, 250)	//Give a little time for connection to settle
//        done()
      })
    })
  },

  saveRest: function (tag, tab, func='save') {	//save or restore a table
    return Format('select wm.table_%s(%L,%L);', func, tab, tag)
  },

  getRow: function (res, idx, exp=1) {
    assert.ok(res)
    assert.equal(res.rowCount, exp)
    return res.rows[idx]
  },

  mkUuid: function(cid, agent, mix = 'x') {	//Build a unique identifier
    let chad = 'chip://' + cid + ':' + agent
      , date = new Date().toISOString()
      , uuid = Uuid.v5(date+mix, Uuid.v5(chad, Uuid.v5.URL))
//    , uuid = Uuid.v5(cid, Uuid.v5.DNS)	//Deterministic
//console.log('date/mix:', date, 'uuid:', uuid)
    return uuid
  },

  importCheck: function(fileName, target, db, done, check) {
    Fs.readFile(fileName, (err, fileData) => {if (err) done(err)
      let jsonData = JSON.parse(fileData)
      db.query("select json.import($1::jsonb, $2::text) as record;", [jsonData, target] ,(err, res) => {
        if (err) done(err)
        assert.equal(res.rowCount, 1)
        let row = res.rows[0]
        assert.ok(row.record)
        if (row.record) check(res,row.record.slice(1,-1).split(','))
      })
    })
  },

  queryJson: function(fileBase, db, sql, done, rows = 1, write = false) {
    let file = Path.join(__dirname, fileBase + '.json')
      , row
    db.query(sql, null, (e, res) => {if (e) done(e)
      if (rows > 1) {
        assert.equal(res.length, rows)
        let resX = res[rows-1]			//;log.debug('resX:', resX)
        assert.equal(resX.rowCount, 1)
        row = resX.rows[0]			//;log.debug('row:', JSON.stringify(row.json))
      } else {
        assert(res.rowCount, 1)
        row = res.rows[0]			//;log.debug("row:", row)
      }
      if (write)
        Fs.writeFileSync(file + '.tmp', JSON.stringify(row.json,null,1))		//Save actual results
      Fs.readFile(file, (e, fData) => {if (e) done(e)
        let expObj = JSON.parse(fData)
        assert.deepStrictEqual(row.json, expObj)
        done()
      })
    })
  }
}

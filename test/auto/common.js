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
const Stringify = require('json-stable-stringify')
const Uuid = require('uuid')
const assert = require('assert');
const Bus = require('./bus')
const DBName = process.env.MyCHIPS_TESTDB ?? "mychipsTestDB"
const devSqlFile = require.resolve('wyseman/lib/develop.sql')
const { DBHost, DBPort, DBAdmin, Log } = require('../settings.js')
const { dbClient } = require("wyseman")
const PeerCont = require("../../lib/peer2peer")
const Crypto = require('../../lib/crypto.js')
const RootDir = Path.join(__dirname, '../../')
const LibDir = Path.join(RootDir, 'lib')
const Schema = Path.join(LibDir, 'schema.json')
const SchemaDir = Path.join(LibDir, '../', 'schema')
const libModule = (m) => Path.join(LibDir, m)

const testLog = function(fname) {	//Initiate a logging service for a mocha test file
    let base = Path.parse(fname).name
      , logName = fname ? 'test-' + base : 'combined.log'
    return Log(logName)
  }
var log = testLog(__filename)

const dockName = 'mychipsTestPG'
const buildDir = Path.join(__dirname, '../..', 'build')
const dockCmd = tag => `docker-compose -p test-${tag} -f ${Path.join(buildDir, `compose-${tag}.yml`)}`
const pgDockCmd = `docker-compose -p test-pg -f ${Path.join(buildDir, 'compose-pg.yml')}`
const pgDockEnv = Object.assign({MYCHIPS_DBHOST: dockName}, process.env)
var pgDockDown
var pgPromise

// -----------------------------------------------------------------------------
function pgCheck(t) {		//Make sure we have a Postgres running
  if (t && t.timeout) t.timeout(10000)	//Set caller's this.timeout
  if (!pgPromise) {
    pgPromise = new Promise((resolve, reject) => {
      let sock = Net.connect(DBPort, DBHost, () => {
log.debug("Found Postgres at:", DBHost, DBPort)
        sock.end()
        resolve(true)
      })
      sock.on('error', e => {		log.debug("checkPG error:", e)
        if (e.code != 'ECONNREFUSED')
          reject(e)
        else {
          let dCmd = dockCmd('pg')
log.debug("Launching docker with compose:", dCmd)
          Child.exec(dCmd + ' up -d', {env: pgDockEnv}, (err,sto,ste) => {	//Launch docker
log.debug("Compose result:", err)
            if (err)
              reject(err)
            else setTimeout(() => {		//Give time for postgres to initialize
log.debug("down: " + dCmd + ' down')
              resolve(true)
            }, 4000)
          })
        }
      })
    })
  }
  return pgPromise
}

// -----------------------------------------------------------------------------
function dockCleanup(done, tag = 'pg') {		//Take down docker process
  let dCmd = dockCmd(tag)
  Child.exec(dCmd + ' down', (err,sto,ste) => {		//Attempt to run docker-compose
    if (!err) log.debug("Stopped docker:", tag)
    done()
  })
}

// -----------------------------------------------------------------------------
function dropDB(done, dbName = DBName) {	//Destroy the test database
  let config = {database:'template1', user: DBAdmin, connect: true, host:DBHost, port:DBPort}
    , sql = Format('drop database if exists "%s";', dbName)
    , db = new dbClient(config, (chan, data) => {}, () => {
    db.query(sql, (e, res) => {if (e) done(e)
      db.disconnect()
      setTimeout(done, 250)	//Give a little time for connection to settle
//      done()
    })
  })
}

// -----------------------------------------------------------------------------
function importCheck(fileName, target, db, done, check) {
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
}

// -----------------------------------------------------------------------------
function develop(db, done) {
  Fs.readFile(devSqlFile, (err, fileData) => {if (err) done(err)
    let sql = fileData.toString()
//log.debug('sql:', sql)
    db.query(sql, null ,(err, res) => {
      if (err) done(err)		//;log.debug('DD:', err, res.rows)
//      assert.equal(res.rowCount, 1)
//      let row = res.rows[0]
//      assert.ok(row.record)
//      if (row.record) check(res,row.record.slice(1,-1).split(','))
      done()
    })
  })
}

// -----------------------------------------------------------------------------
function peerTest(aConf, dConf) {		//Make a peer server with failure test modes
  let serv = new PeerCont(aConf, dConf)
    , oldTransmit = serv.peerTransmit.bind(serv)
    , newTransmit = function(msg, successCB, failureCB) {
this.log.debug("Test peerTransmit", msg.from.cid, '->', msg.to.cid, msg.to.agent)
        if (this.failSend) {				//Force transmission failure
          let c0 = this.failSend.charAt()
          if (c0 == 's' && successCB) successCB()	//Indicate success without sending
          if (c0 == 'f' && failureCB) failureCB()	//Indicate failure as though peer not reach
this.log.debug("Generated error: suppressing send!", this.failSend)
          if (this.failCount && this.failCount > 1) {
            this.failCount--				//;this.log.debug("FailCount", this.failCount)
          } else {
            delete this.failSend			//Clear failure mode
            delete this.failCount
          }
        } else {
          return oldTransmit(msg, successCB, failureCB)
        }
      }
  serv.peerTransmit = newTransmit		//Replace original method
  return serv
}

// -----------------------------------------------------------------------------
function queryJson(fileBase, db, sql, done, rows = 1, write = false) {
  let file = Path.join(__dirname, 'data', fileBase + '.json')
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

// -----------------------------------------------------------------------------
function mkUuid(cid, agent, mix = 'x') {	//Build a unique identifier
  let chad = 'chip://' + cid + ':' + agent
    , date = new Date().toISOString()
    , uuid = Uuid.v5(date+mix, Uuid.v5(chad, Uuid.v5.URL))
//  , uuid = Uuid.v5(cid, Uuid.v5.DNS)	//Deterministic
//console.log('date/mix:', date, 'uuid:', uuid)
  return uuid
}

// -----------------------------------------------------------------------------
module.exports={
  DBName,
  DB2Name: DBName + '2',
  DBAdmin, DBHost, DBPort, Log, dbClient, RootDir, LibDir,
  Format, assert, Bus, testLog, Schema, SchemaDir, Crypto, Stringify,
  pgCheck, dockCleanup, dropDB,
  importCheck, develop, peerTest, queryJson, mkUuid, libModule,

  Data: function(file) {
    return Path.join(__dirname, 'data', file)
  },

  markLogs: function(db, log, done, time=500) {	//Enter a visible marker in DB and server logs
    let mark = 'MARK-------------------->'
    log.debug(mark)
    setTimeout(() => {db.query(mark); done()}, time)
  },

  saveRest: function (tag, tab, func='save') {	//save or restore a table
    return Format('select wm.table_%s(%L,%L);', func, tab, tag)
  },

  getRow: function (res, idx, exp=1) {
    assert.ok(res)
    assert.equal(res.rowCount, exp)
    return res.rows[idx]
  },
  
  dbConf: function(log, listen, database = DBName, schema) {
    Object.assign(this, {
    database, 
    user: DBAdmin, 
    host: DBHost,
    port: DBPort,
    connect: true, log, listen, schema
    })
  },
}

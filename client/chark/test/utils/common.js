// Copied from test/mocha/common.js

const Path = require('path')
const Format = require('pg-format')
const assert = require('assert');
const { dbClient } = require("wyseman")

const { DBHost, DBPort, DBAdmin, Log } = require('../../../../test/settings')

const DBName = 'mychips'

var testLog = function(fname) {		//Initiate a logging service for a mocha test file
  let base = Path.parse(fname).name
    , logName = fname ? 'test-' + base : 'combined.log'
  return Log(logName)
}

module.exports={
  DBName,
  DB2Name: DBName + '2',
  DBAdmin, DBHost, DBPort, Log, dbClient,
  Format, assert, testLog,

  dbConf: function(log, listen, database = DBName) {
    Object.assign(this, {database, user: DBAdmin, connect: true, log, listen })
  },

  getRow: function (res, idx, exp=1) {
    assert.ok(res)
    assert.equal(res.rowCount, exp)
    return res.rows[idx]
  },
}

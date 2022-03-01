const Fs = require('fs')
const Path = require('path')
const Format = require('pg-format')
const Uuid = require('uuid')
const assert = require('assert');
const Bus = require('../bus')
const DBName = "mychipsTestDB"
const { DBHost, DBPort, DBAdmin, Log } = require('../settings.js')
const { dbClient } = require("wyseman")

module.exports={
  DBName,
  DB2Name: DBName + '2',
  DBAdmin, DBHost, DBPort, Log, dbClient,
  Format, assert, Bus,
  Schema: Path.join(__dirname, '../..', 'lib', 'schema.json'),
  dbConf: function(log, listen, database = DBName, schema) {
    Object.assign(this, {database, user: DBAdmin, connect: true, log, listen, schema})
  },
  dropDB: function(done, dbName = DBName) {
    let config = {database:'template1', user: DBAdmin, connect: true}
      , sql = Format('drop database if exists "%s";', dbName)
      , db = new dbClient(config, (chan, data) => {}, () => {
      db.query(sql, (e, res) => {if (e) done(e)
        db.disconnect()
        setTimeout(done, 250)	//Give a little time for connectio to settle
//        done()
      })
    })
  },
  saveRest: function (tag, tab, func='save') {
    return Format('select wm.table_%s(%L,%L);', func, tab, tag)
  },
  getRow: function (res,idx,exp=1) {
    assert(res.rowCount, exp)
    return res.rows[idx]
  },
  mkUuid: function(cid, agent, mix = 'x') {
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
  }
}

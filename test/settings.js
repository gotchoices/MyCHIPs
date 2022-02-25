const Fs = require('fs')
const Path = require('path')
const Format = require('pg-format')
const assert = require('assert');
const Bus = require('./bus')
const Database = "mychipsTestDB"
const DBAdmin = "admin"
const uuidv5 = require('uuid/v5')

module.exports={
  Database,
  Database2: Database + '2',
  DBAdmin,
  DatabaseHost: "localhost",
  DatabasePort: 5432,
  MachineIP: "192.168.56.10",
  AdminID: "r1",
  UserPort: 54320,
  AdminPort: 54320,
  PeerPort: 65430,
  Log: require(require.resolve('wyclif/lib/log.js')),
  Schema: Path.join(__dirname, '..', 'lib', 'schema.json'),
  Format,
  assert,
  Bus,
  dbConf: function(log, listen, database = Database, schema) {
    Object.assign(this, {database, user: DBAdmin, connect: true, log, listen, schema})
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
      , uuid = uuidv5(date+mix, uuidv5(chad, uuidv5.URL))
//    , uuid = uuidv5(cid, uuidv5.DNS)		//Deterministic
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

const Path = require('path')
const Format = require('pg-format')
const assert = require('assert');
const Bus = require('./bus')
const Database = "mychipsTestDB"
const DBAdmin = "admin"
const uuidv5 = require('uuid/v5')

module.exports={
  Database,
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
  dbConf: function(log, listen) {
    Object.assign(this, {database: Database, user: DBAdmin, connect: true, log, listen})
  },
  saveRest: function (tag, tab, func='save') {
    return Format('select wm.table_%s(%L,%L);', func, tab, tag)
  },
  getRow: function (res,idx,exp=1) {
    assert(res.rowCount, exp)
    return res.rows[idx]
  },
  mkUuid: function(cid) {return uuidv5(cid, uuidv5(cid, uuidv5.DNS))}
}

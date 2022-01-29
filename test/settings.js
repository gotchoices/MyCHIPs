const Path = require('path')
const Format = require('pg-format')
const assert = require('assert');
const Bus = require('./bus')
const Database = "mychipsTestDB"
const DBAdmin = "admin"

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
  }  
}

module.exports={
  DatabaseName: "mychipsTestDB",
  DatabaseHost: "localhost",
  DatabasePort: 5432,
  MachineIP: "192.168.56.101",
  DBAdmin: "admin",
  AdminID: "r1",
  UserPort: 54320,
  AdminPort: 54320,
  PeerPort: 65430,
  Log: require(require.resolve('wyclif/lib/log.js')),
}

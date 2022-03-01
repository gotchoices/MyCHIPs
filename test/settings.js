const E = process.env

module.exports={
  DBAdmin:	E.MYCHIPS_DBADMIN	|| "admin",
  DBHost:	E.MYCHIPS_DBHOST	|| "localhost",
  DBPort:	E.MYCHIPS_DBPORT	|| 5432,
  AdminID:	E.MYCHIPS_ADMIN_ID	|| "r1",
  UserHost:	E.MYCHIPS_WSHOST	|| "192.168.56.10",
  UserPort:	E.MYCHIPS_WSPORT	|| 54320,
  AdminPort:	E.MYCHIPS_WSPORT	|| 54320,
  PeerHost:	E.MYCHIPS_AGPORT	|| "localhost",
  PeerPort:	E.MYCHIPS_AGPORT	|| 65430,
  Log: require(require.resolve('wyclif/lib/log.js'))
}

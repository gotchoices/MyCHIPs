const { Schema, dbConf } = require('../common')
const Sites = 4
const SiteBase = 100
const Users = 4
const portBase = 65400
const host = 'localhost'

module.exports = {
  Sites,
  SiteBase,
  Users,
  portBase,
  host,
  tallyData: [
    ['p1000', 'p1001', 4], ['p1001', 'p1002', 5], ['p1002', 'p1003', 6], 
    ['p1000', 'p1101', 10],
    ['p1001', 'p1102', 20],
    ['p1002', 'p1103', 30],
    ['p1100', 'p1101', 4], ['p1101', 'p1102', 5], ['p1102', 'p1103', 6], 
    ['p1100', 'p1201', 10],
    ['p1101', 'p1202', 20],
    ['p1102', 'p1203', 30],
    ['p1200', 'p1201', 4], ['p1201', 'p1202', 5], ['p1202', 'p1203', 6], 
    ['p1200', 'p1301', 10],
    ['p1201', 'p1302', 20],
    ['p1202', 'p1303', 30],
    ['p1300', 'p1301', 4], ['p1301', 'p1302', 5], ['p1302', 'p1303', 6], 
//    ['p1303', 'p1001', 10],
  ],

  initSites: function(log, siteData, userData) {
    for (let idx = 0; idx < Sites; idx++) {	// Make control structure for each site
      let port = portBase + idx
        , agentKey = 'A' + port
        , dbName = 'mychipsTestDB' + idx
        , agent = Buffer.from(agentKey).toString('base64url')
        , aConf = {host, port, keys:{publicKey: agentKey}}
        , dConf = new dbConf(log, undefined, dbName, Schema)
        , site = {idx, dbName, db:null, agent, aConf, dConf}
      siteData[idx] = site			//;log.debug("Site:", idx, site)
      for (let u = 0; u < Users; u++) {		// Control structure for each user
        let type = 'p'
          , num = SiteBase * 10 + idx * SiteBase + u
          , id = type + num
          , cid = 'c_' + idx + '_' + u
          , listen = 'mu_' + id
          , name = 'User ' + id
          , dConf = new dbConf(log, listen, dbName)
          , user = {site, name, type, num, id, cid, agent, dConf}
        userData[id] = user			//;log.debug("User:", user)
      }
    }
  }
}

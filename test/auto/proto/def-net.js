const { Schema, dbConf, fixedKeyPair } = require('../common')
const SiteBase = 100
const Users = 4
const portBase = 65400
const host = 'localhost'
const tallyData = require('./def-nett1')
const Sites = tallyData.reduce((acc, tal) => {
  const [from, to] = tal
  const frSite = parseInt(from[2])
  const toSite = parseInt(to[2])
  const max = frSite > toSite ? frSite : toSite		//;console.log('f:', frSite, 't:', toSite)
  return max > acc ? max : acc
}, 0) + 1						//;console.log('sites:', Sites)

module.exports = {
  Sites,
  SiteBase,
  Users,
  portBase,
  host,
  tallyData,

  initSites: function(log, siteData, userData) {
    for (let idx = 0; idx < Sites; idx++) {	// Make control structure for each site
      let port = portBase + idx
        , dbName = 'mychipsTestDB' + idx
        , keys = fixedKeyPair('A' + port)
        , agent = keys.publicKey.x
        , aConf = {host, port, keys}
        , dConf = new dbConf(log, undefined, dbName, Schema)
        , site = {idx, dbName, db:null, agent, aConf, dConf}	//;log.debug('P:', port, 'A:', agent)
      siteData[idx] = site			//;log.debug("Site:", idx, site)
      for (let u = 0; u < Users; u++) {		// Control structure for each user
        let type = 'p'
          , num = SiteBase * 10 + idx * SiteBase + u
          , id = type + num
          , cuid = 'c_' + idx + '_' + u
          , listen = 'mu_' + id
          , name = 'User ' + id
          , dConf = new dbConf(log, listen, dbName)
          , user = {site, name, type, num, id, cuid, agent, dConf}
        userData[id] = user			//;log.debug("User:", user)
      }
    }
  }
}

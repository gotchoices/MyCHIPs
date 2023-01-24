//Common default settings for mocha tests and sample utilities
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// Local modifications can be made here but in general, try to instead use the
// environment variables shown for each setting.
const E = process.env
const Fs = require('fs')
const Os = require('os')
const Path = require('path')

var defAgent, peerHost, peerPort		//Will be derived from any default agent key found
var defAgentFile = E.MYCHIPS_AGFILE ||
    Path.join(__dirname, '../pki/local', 'default_agent')

if (Fs.existsSync(defAgentFile)) {		//If there is a default agent file built
  let agentText = Fs.readFileSync(defAgentFile)
    , agent = JSON.parse(agentText)
    , key = agent ? agent.key : {}
//console.log('agent:', agent)
  defAgent = key.x				//Draw this information from there
  peerHost = agent.host
  peerPort = agent.port
}

module.exports={
  DBHost:	E.MYCHIPS_DBHOST	|| "localhost",		//Database host
  DBPort:	E.MYCHIPS_DBPORT	|| 5432,		//Database port address
  DBAdmin:	E.MYCHIPS_DBADMIN	|| "admin",		//Aministrator username for
  DBName:	E.MYCHIPS_DBNAME	|| 'mychips',		//Database name
  AdminID:	E.MYCHIPS_ADMIN_ID	|| "r1",		//Internal admin ID
  UserHost:	E.MYCHIPS_WEBHOST	|| Os.hostname(),	//User web/ws host address
  UserPort:	E.MYCHIPS_WSPORT	|| 1025,		//User websocket port
  AdminPort:	E.MYCHIPS_WSPORT	|| 1025,		//Admin websocket port
  PeerHost:	E.MYCHIPS_AGHOST	|| peerHost || "localhost",	//P2P host
  PeerPort:	E.MYCHIPS_AGPORT	|| peerPort || 65430,	//P2P port
  PeerAgent:	E.MYCHIPS_AGENT		|| defAgent,		//P2P agent address
  Log: require(require.resolve('wyclif/lib/log.js'))
}

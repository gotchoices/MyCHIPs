const E = process.env
const Fs = require('fs')
const Path = require('path')

var defAgent, peerHost, peerPort
var defAgentFile = Path.join(__dirname, '../pki/local', 'default_agent')
if (Fs.existsSync(defAgentFile)) {			//If there is a default agent file built
  let agentText = Fs.readFileSync(defAgentFile)
    , agent = JSON.parse(agentText)
    , key = agent ? agent.key : {}
//console.log('agent:', agent)
  defAgent = key.x					//Draw our information from there
  peerHost = agent.host
  peerPort = agent.port
}

module.exports={
  DefAgent:	defAgent,
  DBAdmin:	E.MYCHIPS_DBADMIN	|| "admin",
  DBHost:	E.MYCHIPS_DBHOST	|| "localhost",
  DBPort:	E.MYCHIPS_DBPORT	|| 5432,
  DBName:	E.MYCHIPS_DBNAME	|| 'mychips',
  AdminID:	E.MYCHIPS_ADMIN_ID	|| "r1",
  UserHost:	E.MYCHIPS_WSHOST	|| "192.168.56.10",
  UserPort:	E.MYCHIPS_WSPORT	|| 54320,
  AdminPort:	E.MYCHIPS_WSPORT	|| 54320,
  PeerHost:	E.MYCHIPS_AGPORT	|| peerHost || "localhost",
  PeerPort:	E.MYCHIPS_AGPORT	|| peerPort || 65430,
  Log: require(require.resolve('wyclif/lib/log.js'))
}

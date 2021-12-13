#!/usr/bin/env node
//MyCHIPs production server
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- Only load credentials for services we are actually launching
//- Should serve documents via https to prevent spoofing a document and digest
//- 

const MaxTimeDelta = 60000		//Allow max 1 minute time difference with client's clock
const Os = require('os')
const Path = require('path')
const Fs = require('fs')
const { Args, Dispatch, Log, Credentials, SpaServer} = require('wyclif')
var log = Log('mychips', undefined, process.env.MYCHIPS_LOGPATH || Path.join('/var','tmp','mychips'))
const { Wyseman } = require('wyseman')
var { actions, Parser } = require('wyselib')
Parser(actions, ['../lib/control1', '../lib/control2'].map(f=>require(f)))	//Require our app-specific reports

var argv = Args({
  dbHost:	process.env.MYCHIPS_DBHOST,
  dbPassword:	process.env.MYCHIPS_DBPASSWORD,
  dbName:	process.env.MYCHIPS_DBNAME	|| 'mychips',
  dbPort:	process.env.MYCHIPS_DBPORT	|| 5432,
  dbAdmin:	process.env.MYCHIPS_DBADMIN	|| 'admin',
  clifPort:	process.env.MYCHIPS_WSPORT	|| 54320,
  clifNP:	process.env.MYCHIPS_NPPORT	|| 44320,
  spaPort:	process.env.MYCHIPS_SPAPORT	|| 8000,
  spaKey:	process.env.MYCHIPS_SPAKEY      || Path.join(__dirname, '../pki/local/spa-%.key'),
  spaCert:	process.env.MYCHIPS_SPACERT     || Path.join(__dirname, '../pki/local/spa-%.crt'),
  agentKey:	process.env.MYCHIPS_AGENTKEY    || Path.join(__dirname, '../pki/local/default_agent'),
  dbUserKey:	process.env.MYCHIPS_DBUSERKEY   || Path.join(__dirname, '../pki/local/data-user.key'),
  dbUserCert:	process.env.MYCHIPS_DBUSERCERT  || Path.join(__dirname, '../pki/local/data-user.crt'),
  dbAdminKey:	process.env.MYCHIPS_DBADMINKEY  || Path.join(__dirname, '../pki/local/data-admin.key'),
  dbAdminCert:	process.env.MYCHIPS_DBADMINCERT || Path.join(__dirname, '../pki/local/data-admin.crt'),
  dbCA:		process.env.MYCHIPS_DBUSERCERT  || Path.join(__dirname, '../pki/local/data-ca.crt')
})
  .alias('p','peerPortal').default('peerPortal',false)	//P2p unencrypted connections at this port
  .alias('d','docs')     .default('docs',	true)	//HTML document server
  .alias('l','lifts')    .default('lifts',	false)	//Run lift scheduler
  .alias('m','model')    .default('model',	false)	//Run agent-based model
  .alias('a','agentKey')				//Each peer server runs with a specific agent key
  .argv

//log.debug("argv:", argv)
var credentials = (!argv.noHTTPS && argv.spaPort) ? Credentials(argv.spaKey, argv.spaCert, null, log) : null
var sslAdmin = Credentials(argv.dbAdminKey, argv.dbAdminCert, argv.dbCA)	//Ignore errors
var sslUser = Credentials(argv.dbUserKey, argv.dbUserCert, argv.dbCA)
const pubDir = Path.join(__dirname, "..", "pub")

log.info("SPA Port:   ", argv.spaPort, argv.wyclif, argv.spaKey, argv.spaCert)
log.debug("Server ID:  ", argv.servID)
log.debug("CLIF Ports:  ", argv.clifPort, argv.clifNP)
log.debug("Agent Key:  ", argv.agentKey)
log.debug("Doc Viewer: ", argv.docs)
log.debug("Database:", argv.dbHost, argv.dbName, argv.dbAdmin)
log.trace("Database SSL:", sslAdmin, sslUser)
log.trace("Agent:", argv.model, "Lifts:", argv.lifts)
log.trace("Actions:", actions)

var expApp = SpaServer({
  spaPort: argv.spaPort,
  wyclif: !!argv.wyclif,
  favIconFile: 'favicon.png',
  pubDir, credentials
}, log)

var wyseman = new Wyseman({				//Launch SPA server and associated web socket
  host: argv.dbHost,
  password: argv.dbPassword,
  database:argv.dbName,
  ssl: sslUser,
  user: null, log
}, {
  websock: {port: argv.clifPort, credentials, delta: MaxTimeDelta},
  sock: argv.clifNP, 
  dispatch: Dispatch,
  log, actions, expApp
}, {
  host: argv.dbHost,
  password: argv.dbPassword,
  database:argv.dbName,
  user: argv.dbAdmin,
  connect: true,
  ssl: sslAdmin,
  log, schema: __dirname + "/../lib/schema.json"
})

if (Boolean(argv.agentKey)) {				//Create socket server for peer-to-peer communications
  const PeerCont = require('../lib/peer.js')		//Peer communications controller
  var peerCont
    , openPeerCont = (host, port, key) => {
        peerCont = new PeerCont({host, port, key, poll: true}, {
          host: argv.dbHost,
          database:argv.dbName,
          user: argv.dbAdmin, 
        })
      }
  if (Boolean(argv.peerPortal)) {		//Non-encrypted mode
    let split = argv.peerPortal.toString().split(':')	//In case of host:port given
      , host = split[1] ? split[0] : Os.hostname
      , port = split[1] || argv.peerPort
      , publicKey = Buffer.from(host + ':' + port).toString('base64url')
log.debug("Dummy agent:", host, port, '->', publicKey)
    openPeerCont(host, port, {publicKey})	//Use dummy agent ID

  } else Fs.readFile(argv.agentKey, (err, keyData) => {
    if (err) {log.error("Can't access agent key file:", argv.agentKey); return}
log.debug("agent:", keyData.toString())
    let agent; try {
       agent = JSON.parse(keyData.toString())
    } catch (e) {
      log.error("Can't parse key data in:", argv.agentKey, e.message)
    }
    let jwkKey = agent.key		//JWK has d (private), x (public) properties
      , naclKey = jwkKey ? {
        privateKey: jwkKey.d,
        publicKey: jwkKey.x
      } : null
    openPeerCont(agent.host, agent.port, naclKey)
  })
}

if (Boolean(argv.docs)) {			//Serve up contract documents
  const DocServ = require('../lib/doc.js')
  var docs = new DocServ({
    pubDir, expApp
  }, {
    host: argv.dbHost,
    database:argv.dbName,
    user: argv.dbAdmin, 
  })
}

if (Boolean(argv.lifts)) {				//Run lift scheduler
  const LiftCont = require('../lib/lifts.js')		//Lift controller
  var lifts = new LiftCont()
}

if (Boolean(argv.model)) {				//Run agent-based simulation model
  const AgentCont = require('../lib/agent.js')		//Model controller
  var agent = new AgentCont({
    host: argv.dbHost,
    database:argv.dbName,
    user: argv.dbAdmin, 
  })
}

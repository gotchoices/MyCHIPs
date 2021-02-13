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
  peerKey:	process.env.MYCHIPS_PEERKEY     || Path.join(__dirname, '../pki/local/peer-%.key'),
  peerCert:	process.env.MYCHIPS_PEERCERT    || Path.join(__dirname, '../pki/local/peer-%.crt'),
  dbUserKey:	process.env.MYCHIPS_DBUSERKEY   || Path.join(__dirname, '../pki/local/data-user.key'),
  dbUserCert:	process.env.MYCHIPS_DBUSERCERT  || Path.join(__dirname, '../pki/local/data-user.crt'),
  dbAdminKey:	process.env.MYCHIPS_DBADMINKEY  || Path.join(__dirname, '../pki/local/data-admin.key'),
  dbAdminCert:	process.env.MYCHIPS_DBADMINCERT || Path.join(__dirname, '../pki/local/data-admin.crt'),
  dbCA:		process.env.MYCHIPS_DBUSERCERT  || Path.join(__dirname, '../pki/local/data-ca.crt')
})
  .alias('h','servID')   .default('servID',	null)	//If peer servers run on multiple hosts, this identifies our host
  .alias('p','peerPort') .default('peerPort',	65430)	//Peer-to-peer connections at this port
  .alias('d','docs')     .default('docs',	true)	//HTML document server
  .alias('l','lifts')    .default('lifts',	false)	//Run lift scheduler
  .alias('m','model')    .default('model',	false)	//Run agent-based model
  .argv

//log.debug("argv:", argv)
var credentials = (!argv.noHTTPS && argv.spaPort) ? Credentials(argv.spaKey, argv.spaCert, null, log) : null
var sslAdmin = Credentials(argv.dbAdminKey, argv.dbAdminCert, argv.dbCA)	//Ignore errors
var sslUser = Credentials(argv.dbUserKey, argv.dbUserCert, argv.dbCA)
const pubDir = Path.join(__dirname, "..", "pub")

log.info("SPA Port:   ", argv.spaPort, argv.wyclif, argv.spaKey, argv.spaCert)
log.debug("Server ID:  ", argv.servID)
log.debug("CLIF Ports:  ", argv.clifPort, argv.clifNP)
log.debug("Peer Port:  ", argv.peerPort)
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
  log, schema: __dirname + "/../lib/schema.sql"
})

if (Boolean(argv.peerPort)) {				//Create socket server for peer-to-peer communications
  const PeerCont = require('../lib/peer.js')		//Peer communications controller
  let ssl = Credentials(argv.peerKey, argv.peerCert, null, log)
  var peer = new PeerCont({
    port: argv.peerPort, 
    servID: argv.servID,
    poll: true, ssl
  }, {
    host: argv.dbHost,
    database:argv.dbName,
    user: argv.dbAdmin, 
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

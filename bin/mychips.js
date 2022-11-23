#!/usr/bin/env node
//MyCHIPs production server
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- Only load credentials for services we are actually launching
//- Should serve documents via https to prevent spoofing a document and digest
//- Able to launch without SPA services
//- 
const MaxTimeDelta = 60000		//Allow max 1 minute time difference with client's clock
const Os = require('os')
const Path = require('path')
const Fs = require('fs')
const { Args, Dispatch, Log, Credentials, SpaServer} = require('wyclif')
var log = Log('mychips', undefined, process.env.MYCHIPS_LOGPATH || Path.join('/var','tmp','mychips'))
const { Wyseman } = require('wyseman')
const { actions, Parser } = require('wyselib')
const contDir = '../lib/control'
const controls = Fs.readdirSync(Path.join(__dirname, contDir)).map(f=>(Path.join(contDir, f)))
Parser(actions, controls.map(f=>require(f)))	//Require our app-specific reports

var opts = Args({
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
  dbCA:		process.env.MYCHIPS_DBCA        || Path.join(__dirname, '../pki/local/data-ca.crt')
})
  .alias('d','docs')     .default('docs',	true)	//HTML document server
  .alias('l','lifts')    .default('lifts',	false)	//Run lift scheduler
  .alias('m','model')    .default('model',	false)	//Run agent-based modeler
  .alias('a','agentKey')				//Each peer server runs with a specific agent key
  .argv

//log.debug("opts:", opts)
var credentials = (!opts.noHTTPS && opts.spaPort) ? Credentials(opts.spaKey, opts.spaCert, null, log) : null
var sslAdmin = Credentials(opts.dbAdminKey, opts.dbAdminCert, opts.dbCA)	//Ignore errors
var sslUser = Credentials(opts.dbUserKey, opts.dbUserCert, opts.dbCA)
const pubDir = Path.join(__dirname, "..", "pub")

log.info( "SPA Port:    ", opts.spaPort, opts.wyclif, opts.spaKey, opts.spaCert)
log.debug("CLIF Ports:  ", opts.clifPort, opts.clifNP)
log.debug("Agent Key In:", opts.agentKey)
log.debug("Doc Viewer:  ", opts.docs)
log.debug("Database:    ", opts.dbHost, opts.dbName, opts.dbAdmin)
log.trace("Database SSL:", sslAdmin, sslUser)
log.trace("Modeler:     ", opts.model, "Lifts:", opts.lifts)
log.trace("Actions:     ", actions)

var expApp = new SpaServer({		//Serves up SPA applications via https
  spaPort: opts.spaPort,
  wyclif: !!opts.wyclif,
  favIconFile: 'favicon.png',
  pubDir, credentials
}, log).expApp

var wyseman = new Wyseman({		//Accepts websocket connections from SPA/apps
  host: opts.dbHost,
  password: opts.dbPassword,
  database:opts.dbName,
  ssl: sslUser,
  user: null, log
}, {
  websock: {port: opts.clifPort, credentials, delta: MaxTimeDelta},
  sock: opts.clifNP, 
  dispatch: Dispatch,
  log, actions, expApp
}, {
  host: opts.dbHost,
  password: opts.dbPassword,
  database:opts.dbName,
  user: opts.dbAdmin,
  connect: true,
  ssl: sslAdmin,
  log, schema: __dirname + "/../lib/schema.json"
})

if (Boolean(opts.docs)) {			//Serve up contract documents
  const DocServ = require('../lib/doc.js')
  var docs = new DocServ({
    pubDir, expApp
  }, {
    host: opts.dbHost,
    database:opts.dbName,
    user: opts.dbAdmin, 
  })
}

if (Boolean(opts.agentKey)) {		//Create socket server for peer-to-peer communications
  const PeerCont = require('../lib/peer2peer.js')	//Peer communications controller
  var peerCont
  let log = Log('peer')
    , openPeerCont = (host, port, keys) => {		//Launch peer module
        peerCont = new PeerCont({host, port, keys, log, poll: true}, {
          host: opts.dbHost,
          database:opts.dbName,
          user: opts.dbAdmin, 
        })
      }
  if (/^\w+@[\w.]+:[0-9]+$/.test(opts.agentKey)) {	//Non-encrypted testing mode: agent@host:port
    let [ agent, portal ] = opts.agentKey.split('@')
      , [ host, port ] = portal.split(':')
      , publicKey = Buffer.from(agent, 'base64url')	//if agent length not modulo 4, it may not decode right
    log.debug("Dummy test agent:", publicKey.toString('base64url'), host, port)
    openPeerCont(host, port, {publicKey})		//Use dummy agent ID w/ no private key

  } else Fs.readFile(opts.agentKey, (err, keyData) => {
    if (err) {log.error("Can't access agent key file:", opts.agentKey); return}
    let agent; try {
       agent = JSON.parse(keyData.toString())
    } catch (e) {
      log.error("Can't parse key data in:", opts.agentKey, e.message)
    }
    let jwkKey = agent.key		//JWK has d (private), x (public) properties
      , naclKey = jwkKey ? {
        privateKey:	Buffer.from(jwkKey.d, 'base64url'),
        publicKey:	Buffer.from(jwkKey.x, 'base64url')
      } : null
log.debug("Agent:", jwkKey.x)
    openPeerCont(agent.host, agent.port, naclKey)
  })
}

if (Boolean(opts.lifts)) {				//Run lift scheduler
  const LiftCont = require('../lib/lifts.js')		//Lift controller
  var lifts = new LiftCont()
}

if (Boolean(opts.model)) {				//Run agent-based simulation model
  const AgentCont = require('../lib/agent.js')		//Model controller
  var agent = new AgentCont({
    host: opts.dbHost,
    database:opts.dbName,
    user: opts.dbAdmin, 
  })
}

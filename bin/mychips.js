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

const controls = Fs.readdirSync(Path.join(__dirname, contDir)).filter(el => {
    return Path.extname(el).toLowerCase() == '.js'
  }).map(f => Path.join(contDir, f))
Parser(actions, controls.map(f=>require(f)))	//Require our app-specific reports

var opts = Args(require('../lib/config'))
  .alias('h','home')     .default('home',	true)	//Service Provider HTML Home page
  .alias('d','docs')     .default('docs',	false)	//HTML document server
  .alias('s','scheduler').default('scheduler',	false)	//Run master scheduler
  .alias('m','model')    .default('model',	false)	//Run agent-based modeler
  .alias('a','agentKey')				//Each peer server runs with a specific agent key
  .alias('t','test')     .default('false').boolean('test')	//Do less strict validity checking
  .argv

//log.debug("opts:", opts)
var credentials = (!opts.noHTTPS && opts.uiPort) ? Credentials(opts.webKey, opts.webCert, null, log) : null
var sslAdmin = Credentials(opts.dbAdminKey, opts.dbAdminCert, opts.dbCA)	//Ignore errors
var sslUser = Credentials(opts.dbUserKey, opts.dbUserCert, opts.dbCA)
const pubDir = Path.join(__dirname, "..", "pub")

log.debug("UI Ports:    ", opts.uiPort, opts.clifPort, opts.clifNP)
log.debug("Agent Key In:", opts.agentKey)
log.debug("Web Services:", opts.home, opts.httpPort, opts.httpsPort)
log.debug("Database:    ", opts.dbHost, opts.dbName, opts.dbAdmin)
log.trace("Database SSL:", sslAdmin, sslUser)
log.trace("Modeler:     ", opts.model)
log.trace("Scheduler:   ", opts.scheduler)
log.trace("Actions:     ", actions)

var userExpApp = new SpaServer({	//Serves up SPA applications via https
  uiPort: opts.uiPort,
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
  websock: {port: opts.clifPort, credentials, delta: MaxTimeDelta, uiPort: opts.uiPort},
  sock: opts.clifNP, 
  dispatch: Dispatch,
  expApp: userExpApp,
  log, actions
}, {
  host: opts.dbHost,
  password: opts.dbPassword,
  database:opts.dbName,
  user: opts.dbAdmin,
  connect: true,
  ssl: sslAdmin,
  log, schema: __dirname + "/../lib/schema.json"
})

if (Boolean(opts.home)) {			//Run general web page services
  const CSPHome = require('../lib/csphome.js')
  var cspExpApp = new CSPHome({
    favIconFile: 'favicon.png',
    httpPort: opts.httpPort,		httpsPort: opts.httpsPort,
    smtpHost: opts.smtpHost,		smtpPort: opts.smtpPort,
    dkimKey: opts.dkimKey,		dkimSelect: opts.dkimSelect,
    emailData: opts.cspEmail,
    log, credentials
  }, {
    host: opts.dbHost,
    database:opts.dbName,
    user: opts.dbAdmin, 
  }).expApp

  if (Boolean(opts.docs)) {			//Serve up contract documents
    const DocServ = require('../lib/doc.js')
    var docs = new DocServ({
      pubDir, expApp: cspExpApp
    }, {
      host: opts.dbHost,
      database:opts.dbName,
      user: opts.dbAdmin, 
    })
  }
}

if (Boolean(opts.agentKey)) {		//Create socket server for peer-to-peer communications
  const PeerCont = require('../lib/peer2peer.js')	//Peer communications controller
  let peerCont
  let log = Log('peer')
  Fs.readFile(opts.agentKey, (err, keyData) => {
    if (err) {log.error("Can't access agent key file:", opts.agentKey); return}
    let agentSpec; try {
       agentSpec = JSON.parse(keyData.toString())
    } catch (e) {
      log.error("Can't parse key data in:", opts.agentKey, e.message)
    }
    let {host, port} = agentSpec	//JWK has d (private), x (public) properties
      , privateKey = agentSpec.key
      , publicKey = Object.assign({}, privateKey)
      , agent = publicKey.x
      , keys = {privateKey, publicKey}
    delete publicKey.d				;log.debug("Agent:", agent, JSON.stringify(keys))
    peerCont = new PeerCont({
      agent, host, port, keys, log,
      poll: true,
      test: opts.test
    }, {
      host: opts.dbHost,
      database:opts.dbName,
      user: opts.dbAdmin, 
    })
  })
}

if (Boolean(opts.scheduler)) {				//Run a scheduler
  const Scheduler = require('../lib/scheduler.js')
  var scheduler = new Scheduler({db: {
    host: opts.dbHost,
    database:opts.dbName,
    user: opts.dbAdmin, 
  }})
}

if (Boolean(opts.model)) {				//Run agent-based simulation model
  const AgentCont = require('../lib/model2.js')		//Model controller
  var agent = new AgentCont({
    host: opts.dbHost,
    database:opts.dbName,
    user: opts.dbAdmin, 
  })
}

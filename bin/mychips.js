#!/usr/bin/env node
//MyCHIPs production server
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- 

const MaxTimeDelta = 60000		//Allow max 1 minute time difference with client's clock
const { Args, Dispatch, Log, Credentials, SpaServer} = require('wyclif')
const { Wyseman } = require('wyseman')

var log = Log('mychips')
var { actions, Parser } = require('wyselib')
Parser(actions, ['../lib/control1', '../lib/control2'].map(f=>require(f)))	//Require our app-specific reports

var argv = Args({
  dbHost: process.env.MYCHIPS_DBNAME,
  dbName: process.env.MYCHIPS_DBNAME || 'mychips',
  dbAdmin: process.env.MYCHIPS_DBADMIN || 'admin',
  clifPort: process.env.MYCHIPS_WSPORT || '54320',
  spaPort: process.env.MYCHIPS_SPAPORT || '8000',
  serverKey: process.env.MYCHIPS_SERVER_KEY || __dirname + '/../pki/server_private_key.pem',
  serverCert: process.env.MYCHIPS_SERVER_CERT || __dirname + '/../pki/server_certificate.pem'
})
  .alias('h','hostID')     .default('hostID',     null)		//If peer servers run on multiple hosts, this identifies our host
  .alias('p','peerPort')   .default('peerPort',   65430)	//Peer-to-peer connections at this port
  .alias('l','lifts')      .default('lifts',      false)	//Run lift scheduler
  .alias('m','model')      .default('model',      false)	//Run agent-based model
  .argv

log.debug("argv:", argv)
var credentials = argv.noSSL ? null : Credentials(argv.serverKey, argv.serverCert, log)

log.debug("Host ID:    ", argv.hostID)
log.debug("SPA Port:   ", argv.spaPort, argv.wysegi, argv.serverKey, argv.serverCert)
log.debug("CLIF Port: ", argv.clifPort)
log.debug("Peer Port:  ", argv.peerPort)
log.debug("Database:", argv.dbHost, argv.dbName, argv.dbAdmin)
log.trace("Agent:", argv.model, "Lifts:", argv.lifts)
log.trace("Actions:", actions)

var expApp = SpaServer({spaPort: argv.spaPort, credentials, log})
var wyseman = new Wyseman({
  host: argv.dbHost,
  database:argv.dbName,
  user: null, log
}, {
  port: argv.clifPort, 
  dispatch: Dispatch,
  delta: MaxTimeDelta,
  log, credentials, expApp, actions,
}, {
  host: argv.dbHost,
  database:argv.dbName,
  user: argv.dbAdmin,
  connect: true,
  log, schema: __dirname + "/../lib/schema.sql"
})

if (Boolean(argv.peerPort)) {				//Create socket server for peer-to-peer communications
  const PeerCont = require('../lib/peer.js')		//Peer communications controller
  var peer = new PeerCont(argv.peerPort, argv.hostID, {
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

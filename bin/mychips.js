#!/usr/bin/env node
//MyCHIPs production server
//TODO:
//X- Get simple server running
//X- Optionally launch various servers:
//X-   Admin SPA at https://host:(80)/admin.html
//X-   User SPA at https://host:(80)/user.html
//-   Ticket 1-way tls socket commands at host:port
//-   Admin 2-way tls socket commands at host:port
//-   User 2-way socket commands at host:port
//-   Peer 2-way socket commands at host:port
//-   Public document http server
//- Can't start on fresh database with peerPort enabled (2 simultaneous attempts to create database)
//- 
var	log		= require('../lib/logger')('mychips')
const	Fs		= require('fs')
const	OS		= require('os')
const	Express		= require('express')
const	Http		= require('http')
const	Https		= require('https')
var	expSPApp	= Express()
var	credentials
var	dbConf

var argv = require('yargs')
  .alias('h','hostID')     .default('hostID',     null)		//If peer servers run on multiple hosts, this identifies our host
  .alias('s','spaPort')	   .default('spaPort',    8000)		//Serve client SPA's at this port
  .alias('u','userPort')   .default('userPort',   43210)	//User client at this port
  .alias('a','adminPort')  .default('adminPort',  54320)	//Admin client at this port
  .alias('p','peerPort')   .default('peerPort',   65430)	//Peer-to-peer connections at this port
  .alias('k','serverKey')  .default('serverKey',  null)		//Private SSL key for this server
  .alias('c','serverCert') .default('serverCert', null)		//SSL Certificate for this server
  .alias('D','dbName')	   .default('dbName',     'mychips')	//Database name
  .alias('A','dbAdmin')	   .default('dbAdmin',    'admin')	//Database administrator name
  .alias('H','dbHost')	   .default('dbHost',     null)		//Database administrator name
  .alias('w','wysegi')	   .default('wysegi',     false)	//Serve wysegi SPA
  .alias('l','lifts')      .default('lifts',      false)	//Run lift scheduler
  .alias('m','model')      .default('model',      false)	//Run agent-based model
  .alias('n','noSSL')      .default('noSSL',      false)	//Do not run server with SSL
  .argv

if (!argv.noSSL) {
  let serverKey = argv.serverKey || process.env.MYCHIPS_SERVER_KEY || 'pki/server_private_key.pem'
    , serverCert = argv.serverCert  || process.env.MYCHIPS_SERVER_CERT || 'pki/server_certificate.pem'
    , key = Fs.existsSync(serverKey) ? Fs.readFileSync(serverKey) : null
    , cert = Fs.existsSync(serverCert) ? Fs.readFileSync(serverCert) : null
  if (!key && !cert) log.error("Problem initializing SSL:", serverKey, serverCert)
  credentials = {key, cert}
}
dbConf = {database:argv.dbName, user: argv.dbAdmin, host: argv.dbHost}

log.trace("Host ID:    ", argv.hostID)
log.trace("SPA Port:   ", argv.spaPort, argv.wysegi, argv.serverKey, argv.serverCert)
log.trace("Admin Port: ", argv.adminPort)
log.trace("User Port:  ", argv.userPort)
log.trace("Peer Port:  ", argv.peerPort)
log.trace("Agent:", argv.model, "Lifts:", argv.lifts)
log.trace("dbConf:", dbConf)

if (Boolean(argv.spaPort)) {				//Serve up client SPAs
  let server = credentials ? Https.createServer(credentials, expSPApp) : Http.createServer(expSPApp)

  expSPApp.use(Express.static('pub'))
  if (Boolean(argv.wysegi))
    expSPApp.use(Express.static('node_modules/wylib/dist'))	//Serve up wylib wysegi app too
  expSPApp.get('/clientip', (req, res)=>{		//Let clients know their IP number for validation purposes
//log.trace("Client request:", req.headers)
    date = new Date
    res.send(JSON.stringify({
      ip: req.connection.remoteAddress,
      real: req.headers['x-real-ip'] || req.headers['x-forwarded-for'],
      cookie: req.headers.cookie,
      userAgent: req.headers['user-agent'],
      date,
    }))
  })

  server.listen(argv.spaPort)
  log.debug("Serving client SPA's at port:", argv.spaPort)
}

if (Boolean(argv.adminPort)) {				//Create socket server for admin data
  const AdminCont = require('../lib/admin.js')		//Admin client connection controller
  let wsConf = {port: argv.adminPort, credentials, expApp:expSPApp}
  var admin = new AdminCont(dbConf, wsConf)
}

//if (Boolean(argv.userPort)) {				//Create socket server for user data
//  const UserCont = require('../lib/user.js')		//User client connection controller
//  var user = new UserCont(argv.userPort)
//}

if (Boolean(argv.peerPort)) {				//Create socket server for peer-to-peer communications
  const PeerCont = require('../lib/peer.js')		//Peer communications controller
  var peer = new PeerCont(argv.peerPort, argv.hostID)
}

if (Boolean(argv.lifts)) {				//Run lift scheduler
  const LiftCont = require('../lib/lifts.js')		//Lift controller
  var lifts = new LiftCont()
}

if (Boolean(argv.model)) {				//Run agent-based simulation model
  const AgentCont = require('../lib/agent.js')		//Model controller
  var agent = new AgentCont()
}

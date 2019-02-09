//Admin client controller
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// This module maintains a list of connected admin clients.
// We will receive event packets from clients and apply necessary control logic.
// Applicable changes will be sent to the model, and then relevant updates
// will be propagated back out to any connected clients.
// -----------------------------------------------------------------------------
// TODO:
//- How does Wyseman play into report viewing?
//- Should we move some of this control logic into wyseman?
//- Could listen for certain types of DB notifications to make asynchronous reports
//- 
var log				= require('./logger')('admin')
var fs				= require('fs')
const StringHash		= require('string-hash')
var { Wyseman, dbClient }	= require('wyseman')
const ModuleList		= ['control1', 'control2']
//const ViewerFile		= 'report.html'
var connectionCount		= 0
var controlFunctions		= {}

module.exports = function(dbConf, wsConf) {		//Admin controller module
  let dbAdminConf = Object.assign(dbConf, {
      log,
      schema: __dirname + "/schema-1.sql"
    })
    , dbUserConf = Object.assign(dbConf, {
      log, user:null, listen: ['mychips_admin', 'wylib']
    })

log.debug("In Admin constructor, port:", wsConf.port)
  this.wyseman = new Wyseman(dbUserConf, wsConf, dbAdminConf)		//Establish websocket/db connection for clients
  
//Fixme: move this code to wyseman? (does wysegi need its own actions support?)
  ModuleList.forEach(filename=>{				//Digest the report/action modules we have available
    let bundle = require('./' + filename)
    for (let view in bundle) {					//Consider each view described in the control file
      if (!(view in controlFunctions)) controlFunctions[view] = {}
      Object.assign(controlFunctions[view], bundle[view])
    }
  })
//  for (let view in controlFunctions) {log.debug("Action:", view, Object.keys(controlFunctions[view]))}
}

//Fixme: move this code to wyseman?
// -----------------------------------------------------------------------------
function actionHandler(expApp, db) {		//Make an object to handle action requests from a web socket connection
  this.reportList = {}
  this.connCode = 'R' + (new Date).getTime() + '.' + connectionCount++	//Make unique identifier for this connection handler
  this.path = '/report/' + this.connCode	//Path for resource requests
  this.db = db

log.debug("Path:", this.path)
  expApp.get(this.path + '/:idhash/:resource', (req, res, next)=>{	//Listen for http requests from this action
    let idHash = req.params.idhash
      , resource = req.params.resource
      , id = Object.keys(this.reportList).find(k=>(this.reportList[k].idHash == idHash))
      , reportCache = id ? this.reportList[id] : null			//Find cached info for this report
log.debug("Got http document request:", idHash, id, resource, req.query)
    
    if (reportCache) {
      reportCache.controlFunc(reportCache, (err, content)=>{		//Call our report handler
        if (err) next(err)
        else res.send(content)
      }, resource)
    }
  })
  
  this.handle = function(msg, sender) {			//Process action request coming from UI client
    let {id, action, view, name, data} = msg
log.debug("Got user request:", id, view, name, action, data)
    if (action != 'action' || !(view in controlFunctions) || !(name in controlFunctions[view])) return false
    let actList = controlFunctions[view]		//Look up the specs for this action
      , controlFunc = (actList ? actList[name] : null)
      , reportCache = this.reportList[id]

    if (!controlFunc) return false			//No report found, so abort
    if (!reportCache) {
      let idHash = StringHash(id)
        , resPath = this.path + '/' + idHash
      reportCache = {view, name, data, controlFunc, idHash, db:this.db, path:this.path, resPath}
    }

    if (controlFunc(reportCache, (error, data)=>{	//Generate the report
log.debug('   report generated:', error, 'data:', data)
//      Object.assign(data, {path:this.path, file:ViewerFile})
      sender({id, view, action, name, data, error})	//And return it
    })) {
      this.reportList[id] = reportCache			//Keep a cache of the report parameters
    }
    return true
  }
}

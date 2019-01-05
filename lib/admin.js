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
//- 
var log				= require('./logger')('admin')
var fs				= require('fs')
const StringHash		= require('string-hash')
var { Wyseman, dbClient }	= require('wyseman')
const ModuleList		= ['control1', 'control2']
const ViewerFile		= 'viewer.html'
var instanceCount		= 0
var controlFunctions		= {}

module.exports = function(port, expApp) {			//Admin controller module
log.debug("In Admin constructor, port: " + port)
  this.wyseman = new Wyseman({					//Establish websocket/db connections
    logger: log,
    schema: __dirname + "/schema-1.sql",
    listen: ['mychips_admin', 'wylib'],
  }, {port, actionHandler, expApp})	
  
//Fixme: move this code to wyseman? (does wysegi need actions support?)
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
function actionHandler(expApp) {		//Make an object to handle action requests from a web socket connection
  this.reportList = {}
  this.instCode = 'R' + (new Date).getTime() + '.' + instanceCount++
  this.path = '/report/' + this.instCode
  this.db = new dbClient({logger:log})		//DB connection for reports

log.debug("Path:", this.path)
  expApp.get(this.path + '/:idhash/:resource', (req, res, next)=>{
    let idhash = req.params.idhash
      , resource = req.params.resource
      , id = Object.keys(this.reportList).find(k=>(this.reportList[k].idHash == idhash))
      , reportCache = id ? this.reportList[id] : null
log.debug("Got document request:", idhash, id, resource)
    
    if (reportCache) {
      reportCache.controlFunc(reportCache, (err, content)=>{
        if (err) next(err)
        else res.send(content)
      }, resource)
    }
  })
  
  this.handle = function(msg, sender) {			//Process action request coming from UI client
    let {id, action, view, name, data} = msg
log.debug("Got user request:", id, view, name, action)
    if (action != 'action' || !(view in controlFunctions) || !(name in controlFunctions[view])) return false
    let actList = controlFunctions[view]		//Look up the specs for this action
      , controlFunc = (actList ? actList[name] : null)
      , idHash = StringHash(id)
      , reportCache = {view, name, data, controlFunc, idHash, db:this.db, path:this.path, resPath:this.path + '/' + idHash}
    if (!controlFunc) return false			//No report found, so abort

    if (!controlFunc(reportCache, (data)=>{		//Generate the report
log.debug('   report generated:', data)
      Object.assign(data, {path:this.path, file:ViewerFile})
      sender({id, view, action, name, data})		//And return it
    })) {
      this.reportList[id] = reportCache			//Keep a cache of the report parameters
    }
    return true
  }
}

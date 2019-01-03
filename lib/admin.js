//Admin client controller
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// This module maintains a list of connected admin clients.
// We will receive event packets from clients and apply necessary control logic.
// Applicable changes will be sent to the model, and then relevant updates
// will be propagated back out to any connected clients.
// -----------------------------------------------------------------------------
// TODO:
//- All action modules register view and action name here
//- If we have a handler for the action, create:
//-  Some actions can just be performed and return finished status
//-  Others generate a report preview:
//-   Web endpoint for serving the document
//-   An object that answers the object
//-   And the object receives traffic on this ID
//-   And the object builds the report
//- 
//- Should we really extend Wyseman class, or just keep a pointer to its instance?
//- Open express http server at this level (for document viewer)?
//- How does Wyseman play into document viewing
//- Where/how does the control logic work for building a document report?
//- 
var log			= require('./logger')('admin')
var fs			= require('fs')
var shajs		= require('sha.js')
var { Wyseman }		= require('wyseman')
var express		= require('express')
const ModuleList	= ['control1', 'control2']
const ExpBasePort	= 8100
var expressInstance	= 0
var controlFunctions	= {}
const htmlContainer	= `
<!DOCTYPE html><html>
  <head>
    <title>Wylib Report Wrapper</title>
    <script>
      function init() {
        window.addEventListener("message", function(event) {
          if (event.data == 'reload') window.location.reload()
        })
      }
    </script>
  </head>
  <body onload="init()">
    <h4>Report:</h4>
    <span>__NUMBER__</span>
    <embed src="__SRC_FILE__" width="400" height="600" type="__MIME_TYPE__">
    </embed>
  </body>
</html>
`

module.exports = function(port) {
log.debug("In Admin constructor, port: " + port)
  let dbConf = {
    logger: require('../lib/logger')('admin'),
    schema: __dirname + "/schema-1.sql",
    listen: ['mychips_admin', 'wylib']
  }
  this.wyseman = new Wyseman(dbConf, port, actionHandler)	//Establish websocket/db connections

  ModuleList.forEach(filename=>{				//Digest the report/action modules we have available
    let bundle = require('./' + filename)
    for (let view in bundle) {
      if (!(view in controlFunctions)) controlFunctions[view] = {}
      let actList = bundle[view]
      for (let act in actList) {
        let spec = actList[act]
        if (typeof spec == 'function') actList[act] = {report: false, builder: spec}
log.debug("  Action Config:", view, spec)
      }
      Object.assign(controlFunctions[view], bundle[view])
    }
  })
  for (let view in controlFunctions) {log.debug("Action:", view, Object.keys(controlFunctions[view]))}
}

function actionHandler() {	//Make an object to handle action requests from a web socket
  this.reportList = {}
  this.docNumber = 1
  this.expInst = expressInstance++
  this.expApp = express()
  this.expPort = ExpBasePort + this.expInst
  this.expPath = '/report/' + this.expInst
  this.expApp.listen(this.expPort)
log.debug("Express listening on:", this.expPort, "path:", this.expPath)
  this.expApp.get(this.expPath + '/:file', (req, res)=>{
log.debug("Got document request:", req.params.file)
    let file = req.params.file
      , [ base, ext ] = file.split('.')
      , id = Object.keys(this.reportList).find(k=>(this.reportList[k].file == base))
      , report = this.reportList[id]
log.debug("  id:", id)
     if (!report) return
     if (!ext) {
       let doc = htmlContainer.replace('__MIME_TYPE__', report.mime)
         .replace('__SRC_FILE__', file + '.' + report.format)
         .replace('__NUMBER__', this.docNumber++)
log.debug("  send wrapper:", base)
       res.send(doc)
     } else {
log.debug("  send:", file)
       res.send(report.contents)
     }
  })
  
  this.handle = function(msg, sender) {
    let {id, action, view, name, data, keys} = msg
log.debug("Got user request:", id, view, name, action, keys)
    if (action != 'action' || !(view in controlFunctions) || !(name in controlFunctions[view])) return false
    let actList = controlFunctions[view]
      , spec = (actList ? actList[name] : null)
      , retData = {}
      , report
log.debug("  Action:", name, Object.keys(spec))
    if (!spec) return false				//No report found
    if (!spec.report) {					//Immediate action, no preview
log.debug('   Immediate:', spec.builder)
      if (typeof spec.builder == 'function') {
        retData.status = 'success'
        spec.builder(keys, data, (contents)=>{
          sender({id, view, action, name, data:retData})
        })
      }
      return true
    } else if (id in this.reportList) {
      report = this.reportList[id]
log.debug('   Already:', this.reportList[id].fileName)
      Object.assign(retData, {status: 'reload', port: report.port, path:report.path, file:report.file})
    } else {
      let file = shajs('sha1').update(Math.Random * (2^16)).digest('hex')
        , path = this.expPath
      report = this.reportList[id] = {file, path, builder:spec.builder, port:this.expPort, format:spec.format}
      Object.assign(retData, {status: 'open', port: this.expPort, path, file})
log.debug('   New:', path, file)
    }
    report.builder(keys, data, (contents)=>{
log.debug('   report generated:', contents)
      report.contents = contents
      sender({id, view, action, name, data:retData})
    })
    return true
  }
  
  this.close = function() {
  }
}

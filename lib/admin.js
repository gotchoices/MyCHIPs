//Admin client controller
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// This module maintains a list of connected admin clients.
// We will receive event packets from clients and apply necessary control logic.
// Applicable changes will be sent to the model, and then relevant updates
// will be propagated back out to any connected clients.
// -----------------------------------------------------------------------------
// TODO:
//- Should we really extend Wyseman, or just keep a pointer to its instance?
//- Open express http server at this level (for document viewer)?
//- How does Wyseman play into document viewing
//- Where/how is control logic for building a document report?
//- 
var log = require('./logger')('admin')
var fs		= require('fs')
var { Wyseman }	= require('wyseman')
var express	= require('express')
const ExpPort	= 8001

//const lookup = {
//  user_list: "select id,std_name,user_cdi,user_hid from mychips.users_v",
//  doc_list: "select * from mychips.docs_v",
//  import: (data) => {
//    log.debug("File importer: ", data)
//  },
//}

module.exports = class AdminControl extends Wyseman {
  constructor(port) {
log.debug("In Admin constructor, port: " + port)
    let dbConf = {
      logger: require('../lib/logger')('admin'),
      interface: require('./interface'),
      schema: __dirname + "/schema-1.sql"
    }
    super(dbConf, port, (msg, sender) => {this.controlHandler(msg, sender)})
    
//    this.expApp = express()
//    this.expApp.listen(ExpPort)
//    this.number = 99
//    this.expApp.get('/doc', (req, res) => {
//log.debug("Got doc request")
//      res.send("Here's your doc: " + this.number)
//    })
//    setInterval(() => {this.number--}, 1000)
  }

  controlHandler(msg, sender) {
// Put any admin-specific control handlers here (which return true if action matched)
    let {id, action} = msg
log.debug("Got user request:", msg)
    if (action == "viewer") {
log.debug("  for viewer")
      return true
    } else {
      return false
    }
  }
}

//    if (tag == 'listen') tag = data;		//Just push the tag the client is listening to
//    if (lookup[tag]) {				//If we have a handler for this command
//      if (typeOf(lookup[tag])) {}
//    }

//    if (tag == 'listen' && data == 'user_list') {
//      this.db.query("select id,std_name,user_cdi,user_hid from mychips.users_v", (res) => {
//log.debug("res:" + JSON.stringify(res.rows))
//        this.sender({tag: 'user_list', data: res.rows})
//      })
//    }

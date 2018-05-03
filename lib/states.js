//State machine controller
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// An agent consists of one or more state variables
// This module will track the state of one of those variables in accordance
// with a pre-defined state transition structure.
// -----------------------------------------------------------------------------
// TODO:
//- Make simple state transition structure
//- Implement state interpreter/transition machine
//- Make framework for spawning/tracking separate agents
//- 
var log = require('./logger')('states')
var fs		= require('fs')
//var Wyseman	= require('wyseman')
//var express	= require('express')

const stsSample1 = {
  timeout: begin,
  error: begin,
  begin: {
    success: step1,
    failure: begin,
  },
  step1: {
    success: step1,
    failure: begin,
  },
  step2: begin,
    success: begin,
    failure: begin,
  },
}

const stsSample2 = function(event) {
  switch (event) {
    timeout: 'begin',
  begin: {
    
  },
}

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

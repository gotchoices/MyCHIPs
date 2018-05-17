//State machine controller
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// An agent consists of one or more state variables
// This module will track the state of one of those variables in accordance
// with a pre-defined state transition structure.
// -----------------------------------------------------------------------------
// TODO:
//X- Make simple state transition structure
//- Implement state interpreter/transition machine
//- Can run on a specified state map
//- Make framework for spawning/tracking separate agents
//- 
//- Tally specific:
//- Handle dialog between user SPA and server
//- Implement chit dialogs
//- Implement lift dialogs
//- 
var log = require('./logger')('states')
//var fs	= require('fs')
//var Wyseman	= require('wyseman')
//var express	= require('express')

module.exports = class StateMachine {
  constructor(map) {
log.debug("In state machine constructor, map:", Object.keys(map))
     this.map = map
  }

  handle(action) {
log.debug('Handling action:', action)
  }
}

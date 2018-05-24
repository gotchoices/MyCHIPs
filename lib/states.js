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
  constructor(context, map, dbCallback) {
//log.debug("In state machine constructor, map:", Object.keys(map))
     this.context = context
     this.map = map
     this.dbCallback = dbCallback
  }

  handle(action, msg) {
    log.trace('Handling state action:', action)
    if (action in this.map) {
      var recipe = this.map[action]
      if ('pre' in recipe && typeof(recipe.pre) == 'function') {
        log.trace("Found pre function")
        recipe.pre.call(this.context, msg)
      }
      if ('db' in recipe) {
        log.trace("Found db:", recipe.db)
        this.dbCallback.call(this.context, msg, recipe.db)
      }
      if ('post' in recipe && typeof(recipe.post) == 'function') {
        log.trace("Found post function")
        recipe.pre.call(this.context, msg)
      }
    }
  }
}

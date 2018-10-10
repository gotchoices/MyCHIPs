//State machine map for tallies
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
//- TODO:
//- 
//- 

module.exports = function(id, db, logger) {
  this.id = id
  this.db = db
  this.log = require('../../lib/logger')('agent_' + id)
  this.maxStocks = Math.trunc(Math.random() * 3.0)		//How many stocks (income sources) I will try to maintain
  this.maxFoils = Math.trunc(Math.random() * 10.0)		//And how many foils (expense sinks)
  
  this.iterate = function() {
    this.log.debug("Iterate for user agent:", this.id)
  }
}

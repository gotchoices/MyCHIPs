//State machine map for pathway route discovery
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//- TODO:
//- Include validity checks on incoming packets (see Fixme's below)
//- Include state handlers for stale, none (other) route states
//- 
//A partial, external pathway is represented by a record in mychips.routes.  It 
//indicates the state of an actual such pathway, or query about a hypothetical 
//such pathway, that may exist on other servers external to our own database.
//
//Use cases:
//- A user initiates a (typically conditional) request to lift to a peer 
//  somewhere on the network.  The peer might not yet be known by our database.
//- A tally is created with an upstream, outside peer known to our database, 
//  and we need to know if there are any routes through that peer that lead back 
//  to a downstream peer known to our database.
//- A downstream system has asked us if we have a way to reach a peer specified
//  by an obscured ID, and a host address.
//- An existing pathway has failed before or is stale and it is time to retry.
//- Existing pathway(s) are not supporting the size or volume of lifts our
//  users require so we want to develop more options.
//
// Unlike tallies and chits, pathway state changes don't always create 
// notifications to be transmitted to the end user.  The events that drive 
// state transitions are:
// - Triggers firing within the database
// - Polling by the server for stale records, ripe retries, etc.
// - Reactions to message received from peer servers
// 
//A route record can have the following states:
//  null/void:		status=void,	tries=0,	(or no request yet)
//  draft:		status=draft,
//  pend:		status=pend,			time < exp_date
//  timeout:		status=pend,	0>tries<max	time >= exp_date
//  unknown:		status=pend,	tries>=max	time >= exp_date
//  good:		status=good,			time > exp_date
//  stale:		status=good,			time >= exp_date
//  none:		status=none,
//
const { Log } = require('wyclif')
var log = Log('path')

module.exports = {
  local: {					//Actions invoked from local DB notices
    draft: function(msg) {			//A draft tally has been created or modified by the user
//this.log.debug("In draft handler:", JSON.stringify(msg))
      let pmsg = Object.assign({}, msg, {action: 'query'})
      delete pmsg.reverse; delete pmsg.back
      this.peerTransmit(pmsg, ()=>{		//Action: transmit path query to peer
        this.dbProcess(msg, {			//If context = userDraft, set status = 'draft'
          context:	['draft'],
          update:	{status: 'pend'}
        }, null, e=>this.dbError(msg,e))
      }, e=>this.peerError(msg,e))
    },
    good: function(msg) {			//Route has been marked as good in the database
//this.log.trace("in good handler:", JSON.stringify(msg))
        let pmsg = Object.assign({}, msg, {at:msg.back, back:msg.at, 'object':msg.reverse, action:'affirm'})
        delete pmsg.step; delete pmsg.reverse
//this.log.debug("In good handler:", JSON.stringify(pmsg))
      this.peerTransmit(pmsg, null, e=>this.peerError(msg,e))
    },
    none: function(msg) {			//Route has been marked as none in the database
//this.log.trace("in none handler:", JSON.stringify(msg))
        let pmsg = Object.assign({}, msg, {at:msg.back, back:msg.at, 'object':msg.reverse, action:'fail'})
        delete pmsg.step; delete pmsg.reverse
//this.log.debug("In none handler:", JSON.stringify(pmsg))
      this.peerTransmit(pmsg, null, e=>this.peerError(msg,e))
    },
  },

  remote: {
    query: function(msg, servSock) {			//A peer server has asked for route information
// Fixme: Insert validity checks/limits here
//this.log.debug("In query handler:", servSock, JSON.stringify(msg))
      this.dbProcess(msg, {
        context:	['null','void','timeout','unknown'],
        query:		''
      }, action=>{
        if (action == 'affirm' || action == 'fail') {	//Return success/failure to sender without further state action
          let pmsg = Object.assign({}, msg, {at:msg.here, here:msg.at, action})
//this.log.debug("Query resolved:", action, JSON.stringify(pmsg))
          delete pmsg.step; delete pmsg.try		//Fixme: anything else to delete?
          this.peerTransmit(pmsg, null, e=>this.peerError(msg,e))
        }
      }, e=>this.dbError(msg,e))
    },
    affirm: function(msg) {			//The partner can perform the requested route
// Fixme: Insert validity checks/limits here
//this.log.debug("In affirm:", JSON.stringify(msg))
      this.dbProcess(msg, {
        context: ['pend', 'timeout', 'unknown'],
        update: {status: 'good'}
      }, null, e=>this.dbError(msg,e))
    },
    fail: function(msg) {			//The partner says the route fails somehow
// Fixme: Insert validity checks/limits here
//this.log.debug("In fail:", JSON.stringify(msg))
      this.dbProcess(msg, {
        context: ['pend', 'timeout', 'unknown'],
        update: {status: 'none'}
      }, null, e=>this.dbError(msg,e))
    },
  }
}

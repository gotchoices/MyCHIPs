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
var log = Log('route')

module.exports = {
  local: {					//Actions invoked from local DB notices
    draft: function(msg) {			//A draft route record has been created
log.debug("Local draft:", JSON.stringify(msg))
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
//log.trace("in good handler:", JSON.stringify(msg))
        let pmsg = Object.assign({}, msg, {at:msg.back, back:msg.at, 'object':msg.reverse, action:'affirm'})
        delete pmsg.step; delete pmsg.reverse
log.debug("Local good:", JSON.stringify(pmsg))
      this.peerTransmit(pmsg, null, e=>this.peerError(msg,e))
    },

    none: function(msg) {			//Route has been marked as not possible in the database
//log.trace("in none handler:", JSON.stringify(msg))
        let pmsg = Object.assign({}, msg, {at:msg.back, back:msg.at, 'object':msg.reverse, action:'fail'})
        delete pmsg.step; delete pmsg.reverse
log.debug("Local none:", JSON.stringify(pmsg))
      this.peerTransmit(pmsg, null, e=>this.peerError(msg,e))
    },
  },

  remote: {					//Actions caused by a received peer packet
    query: function(msg, servSock) {		//A downstream peer server has asked for route information
// Fixme: Insert validity checks/limits here
      msg.step++
log.debug("Remote query:", servSock, JSON.stringify(msg))
      this.dbProcess(msg, {
        context:	['null','void','timeout','unknown'],
        query:		''
      }, result=>{
        let [ action, lading ] = result.split('|')		//Get payload from response, if any
//log.debug("Query action:", result, 'a:', action, 'l:', lading)
        if (lading) try {lading = JSON.parse(lading)} catch(e) {lading = {}}
        if (action == 'affirm' || action == 'fail') {		//Return success/failure to sender without further state action (there is no local route record to act upon or trigger from)
          let pmsg = Object.assign({}, msg, {at:msg.here, here:msg.at, action})		//Reverse message direction
          Object.assign(pmsg.object, {lading})
log.debug(" query resolved:", action, JSON.stringify(pmsg))
          delete pmsg.try					//Fixme: anything else to delete?
          this.peerTransmit(pmsg, null, e=>this.peerError(msg,e))
        }
      }, e=>this.dbError(msg,e))
    },

    affirm: function(msg) {			//The upstream partner can perform the requested route
// Fixme: Insert more validity checks/limits here
      let lading = (({lmin,lmargin,lmax,lreward,dmin,dmargin,dmax,dreward})=>{
        return {
          lift_min: lmin,	lift_margin: lmargin,
          lift_max: lmax,	lift_reward: lreward,
          drop_min: dmin,	drop_margin: dmargin,
          drop_max: dmax,	drop_reward: dreward
        }
      }) (msg.object.lading || {})
log.debug("Remote affirm:", JSON.stringify(msg), "lading:", lading)
      this.dbProcess(msg, {
        context: ['pend', 'timeout', 'unknown'],
        update: Object.assign({status: 'good'}, lading)
      }, null, e=>this.dbError(msg,e))
    },

    fail: function(msg) {			//The upstream partner says the route fails somehow
// Fixme: Insert validity checks/limits here
log.debug("Remote fail:", JSON.stringify(msg))
      this.dbProcess(msg, {
        context: ['pend', 'timeout', 'unknown'],
        update: {status: 'none'}
      }, null, e=>this.dbError(msg,e))
    },
  }
}

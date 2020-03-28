//State machine map for distributed lift execution
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// See doc/Lifts for a more detailed description of the lift algorithm.
//- TODO:
//- Port from route.js
//- 
//
//A lift record can have the following states:
//  null/void:		status=void,			(or no record yet)
//  init:		status=init,
//  seek:		status=seek,
//  timeout:		status=seek,			time >= exp_date
//  failed:		status=failed,
//  pend:		status=pend,
//  closed:		status=closed,
//
const { Log } = require('wyclif')
var log = Log('lift')

module.exports = {
  local: {					//Actions invoked from local DB notices
    init: function(msg) {			//A draft route record has been created
log.debug("Local init:", JSON.stringify(msg))
      let pmsg = Object.assign({}, msg, {action: 'query'})
//      delete pmsg.reverse; delete pmsg.back
      this.peerTransmit(pmsg, ()=>{		//Action: transmit path query to peer
        this.dbProcess(msg, {			//If context = userDraft, set status = 'draft'
          context:	['draft'],
          update:	{status: 'seek'}
        }, null, e=>this.dbError(msg,e))
      }, e=>this.peerError(msg,e))
    },

//    good: function(msg) {			//Route has been marked as good in the database
//log.trace("in good handler:", JSON.stringify(msg))
//        let pmsg = Object.assign({}, msg, {at:msg.back, back:msg.at, 'object':msg.reverse, action:'affirm'})
//        delete pmsg.step; delete pmsg.reverse
//log.debug("Local good:", JSON.stringify(pmsg))
//      this.peerTransmit(pmsg, null, e=>this.peerError(msg,e))
//    },

//    none: function(msg) {			//Route has been marked as not possible in the database
//log.trace("in none handler:", JSON.stringify(msg))
//        let pmsg = Object.assign({}, msg, {at:msg.back, back:msg.at, 'object':msg.reverse, action:'fail'})
//        delete pmsg.step; delete pmsg.reverse
//log.debug("Local none:", JSON.stringify(pmsg))
//      this.peerTransmit(pmsg, null, e=>this.peerError(msg,e))
//    },
  },

  remote: {					//Actions caused by a received peer packet
    query: function(msg, servSock) {		//A downstream peer server has asked for route information
// Fixme: Insert validity checks/limits here
log.debug("Remote lift query:", servSock, JSON.stringify(msg))
//      this.dbProcess(msg, {
//        context:	['null','void','timeout','unknown'],
//        query:		''
//      }, result=>{
//        let [ action, lading ] = result.split('|')		//Get payload from response, if any
//log.debug("Query action:", result, 'a:', action, 'l:', lading)
//        if (lading) try {lading = JSON.parse(lading)} catch(e) {lading = {}}
//        if (action == 'affirm' || action == 'fail') {		//Return success/failure to sender without further state action (there is no local route record to act upon or trigger from)
//          let pmsg = Object.assign({}, msg, {at:msg.here, here:msg.at, action})		//Reverse message direction
//          Object.assign(pmsg.object, {lading})
//log.debug(" query resolved:", action, JSON.stringify(pmsg))
//          delete pmsg.try					//Fixme: anything else to delete?
//          this.peerTransmit(pmsg, null, e=>this.peerError(msg,e))
//        }
//      }, e=>this.dbError(msg,e))
    },

//    affirm: function(msg) {			//The upstream partner can perform the requested route
// Fixme: Insert more validity checks/limits here
//      let lading = (({lmin,lmargin,lmax,lreward,dmin,dmargin,dmax,dreward})=>{
//        return {
//          lift_min: lmin,	lift_margin: lmargin,
//          lift_max: lmax,	lift_reward: lreward,
//          drop_min: dmin,	drop_margin: dmargin,
//          drop_max: dmax,	drop_reward: dreward
//        }
//      }) (msg.object.lading || {})
//log.debug("Remote affirm:", JSON.stringify(msg), "lading:", lading)
//      this.dbProcess(msg, {
//        context: ['pend', 'timeout', 'unknown'],
//        update: Object.assign({status: 'good'}, lading)
//      }, null, e=>this.dbError(msg,e))
//    },

//    fail: function(msg) {			//The upstream partner says the route fails somehow
// Fixme: Insert validity checks/limits here
//log.debug("Remote fail:", JSON.stringify(msg))
//      this.dbProcess(msg, {
//        context: ['pend', 'timeout', 'unknown'],
//        update: {status: 'none'}
//      }, null, e=>this.dbError(msg,e))
//    },
  }
}

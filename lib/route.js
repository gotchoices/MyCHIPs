//State machine map for pathway route discovery
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//- TODO:
//- Should there be more validity checks on incoming remote packets?
//- 
const { Log } = require('wyclif')
var log = Log('route')

module.exports = {
  local: {					//Actions invoked from local DB notices
    draft: function(msg) {			//A draft route record has been created
log.debug("Local draft:", JSON.stringify(msg))
      let pmsg = Object.assign({}, msg, {action: 'query'})
      this.peerTransmit(pmsg, ()=>{		//Action: transmit path query to peer
        let dmsg = Object.assign({}, msg, {to:msg.from, from:msg.to})
        this.dbProcess(dmsg, {			//If context = userDraft, set status = 'draft'
          context:	['draft'],
          update:	{status: 'pend'}
        }, null, e=>this.dbError(dmsg,e))
      }, e=>this.peerError(pmsg,e))
    },

    good: function(msg) {			//Route has been marked as good in the database
log.debug("Local good:", JSON.stringify(msg))
//log.debug("  good pmsg:", JSON.stringify(pmsg))
      this.peerTransmit(msg, null, e=>this.peerError(msg,e))
    },

//Probably shouldn't propagate none's back downstream as there may be a mix of good's and none's 
//coming from various upstream routes.  Better to let downstreamers know only of goods and let
//the lack of good's simply leave route queries in pend mode until they time out.
//    none: function(msg) {			//Route has been marked as not possible in the database
//log.debug("Local none:", JSON.stringify(msg))
//      this.peerTransmit(msg, null, e=>this.peerError(msg,e))
//    },
  },

  remote: {				//Actions caused by a received peer packet
    query: function(msg) {		//A downstream peer server has asked for route information
      let obj = msg.object
      if (!('step' in obj)) obj.step = 0	//Make sure we have a valid step parameter
      obj.step++			//Increment each time forwarded

// Fixme: Any more validity checks/limits here before sending to DB?
log.debug("Remote query:", JSON.stringify(msg))
      this.dbProcess(msg, {
        context:	['null','none','good.X','pend.X'],
        query:		true
      }, result=>{
        let { action, lading } = result		//Get payload from response, if any
//log.debug("Query action:", result, 'a:', action, 'l:', lading)
        if (action == 'good' || action == 'none') {		//Return success/failure to sender without further state action (there is no local route record to act upon or trigger from)
          let pmsg = Object.assign({}, msg, {to:msg.from, from:msg.to, action})		//Reverse message direction
          Object.assign(pmsg.object, {lading})
//log.debug(" query resolved:", action, JSON.stringify(pmsg))
          delete pmsg.try					//Fixme: anything else to delete?
          this.peerTransmit(pmsg, null, e=>this.peerError(pmsg,e))
        }
      }, e=>this.dbError(msg,e))
    },

    good: function(msg) {			//The upstream partner can perform the requested route
// Fixme: Any more validity checks/limits here before sending to DB?
log.debug("Remote good:", JSON.stringify(msg))
      let lading = (({lmin,lmargin,lmax,lreward,dmin,dmargin,dmax,dreward})=>{
        return {
          lift_min: lmin,	lift_margin: lmargin,
          lift_max: lmax,	lift_reward: lreward,
          drop_min: dmin,	drop_margin: dmargin,
          drop_max: dmax,	drop_reward: dreward
        }
      }) (msg.object.lading || {})
//log.debug("  good dmsg:", JSON.stringify(msg), "lading:", lading)
      this.dbProcess(msg, {
        context: ['none', 'pend', 'pend.X', 'good.X'],
        update: Object.assign({status: 'good'}, lading)
      }, null, e=>this.dbError(msg,e))
    },

    none: function(msg) {			//The upstream partner says the route fails somehow
// Fixme: Any more validity checks/limits here before sending to DB?
log.debug("Remote none:", JSON.stringify(msg))
      this.dbProcess(msg, {
        context: ['none', 'pend', 'pend.X', 'good.X'],
        update: {status: 'none'}
      }, null, e=>this.dbError(msg,e))
    },
  }
}

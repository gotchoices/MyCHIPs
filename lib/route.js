//State machine map for pathway route discovery
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//- TODO:
//- Should there be more validity checks on incoming remote packets?
//- 
const { Log } = require('wyclif')
var log = Log('route')

module.exports = function() {
  this.local_draft = function(msg, pm) {	//A draft route record has been created
log.debug("Local draft:", JSON.stringify(msg))
    let pmsg = Object.assign({}, msg, {action: 'query'})
    pm.peerTransmit(pmsg, ()=>{		//Action: transmit path query to peer
      let dmsg = Object.assign({}, msg, {to:msg.from, from:msg.to})
      pm.dbProcess(dmsg, {			//If context = userDraft, set status = 'draft'
        context:	['draft'],
        update:	{status: 'pend'}
      }, null, e=>pm.dbError(dmsg,e))
    }, e=>pm.peerError(pmsg,e))
  }

  this.local_good = function(msg, pm) {		//Route has been marked as good in the database
log.debug("Local good:", JSON.stringify(msg))
//log.debug("  good pmsg:", JSON.stringify(pmsg))
    pm.peerTransmit(msg, null, e=>pm.peerError(msg,e))
  }

 this.remote_query = function(msg, pm) {	//A downstream peer server has asked for route information
    let obj = msg.object
    if (!('step' in obj)) obj.step = 0	//Make sure we have a valid step parameter
    obj.step++			//Increment each time forwarded

// Fixme: Any more validity checks/limits here before sending to DB?
log.debug("Remote query:", JSON.stringify(msg))
    pm.dbProcess(msg, {
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
        pm.peerTransmit(pmsg, null, e=>pm.peerError(pmsg,e))
      }
    }, e=>pm.dbError(msg,e))
  }

  this.remote_good = function(msg, pm) {	//The upstream partner can perform the requested route
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
    pm.dbProcess(msg, {
      context: ['none', 'pend', 'pend.X', 'good.X'],
      update: Object.assign({status: 'good'}, lading)
    }, null, e=>pm.dbError(msg,e))
  }

  this.remote_none = function(msg, pm) {	//The upstream partner says the route fails somehow
// Fixme: Any more validity checks/limits here before sending to DB?
log.debug("Remote none:", JSON.stringify(msg))
    pm.dbProcess(msg, {
      context: ['none', 'pend', 'pend.X', 'good.X'],
      update: {status: 'none'}
    }, null, e=>pm.dbError(msg,e))
  }
}

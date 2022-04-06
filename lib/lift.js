//State machine map for distributed lift execution
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// See doc/Lifts for a more detailed description of the lift algorithm.
// TODO:
//- Add support for linear lifts in local.found()
//-   Use tally chain as constituted, update payment info in record
//- Handle errors in badly formed incoming messages
//- 
//- Init: decide what/if referee to use
//- Init: encrypt 'from' property using noise protocol
//- Launch timeout timer
//- 
//- 
const { Log } = require('wyclif')
var log = Log('lift')
const Uuid = require('uuid')
//const Stringify = require('json-stable-stringify')
//const Hash = require('hash.js')

const mkUuid = function(cid, agent, mix = 'x') {
  let chad = 'chip://' + cid + ':' + agent
    , date = new Date().toISOString()
    , uuid = Uuid.v5(date+mix, Uuid.v5(chad, Uuid.v5.URL))
  return uuid
}

const encrypt = function(obj, agent) {		//Fixme: insert actual noise encryption here
  return Buffer.from(JSON.stringify(obj)).toString('base64url')
}
const decrypt = function(str) {		//Fixme: insert actual noise decryption here
  let plain = Buffer.from(str, 'base64url').toString()
    , obj = JSON.parse(plain)
  return obj
}

module.exports = {
  local: {					//Actions invoked from local DB notices
    init: function(msg) {			//A draft lift record has been created locally
log.debug("Local init:", msg)
      let { org, ref, find, circuit } = msg.init	//With default values for org,ref,find
        , { target, topc, object, sequence } = msg	//Grab message components
        , lift_uuid = mkUuid(topc.cid, topc.agent)	//Permanent uuid
        , dmsg = {target, sequence, object}		//Make minimal return message for DB
      org.plan = encrypt(org.plan, find.agent)
//log.debug("  dmsg:", JSON.stringify(dmsg, null, 2))
      this.dbProcess(dmsg, {			//Update DB with origin, referee, find
        context:	['draft.init'],
        update:	{status: 'init', request: 'seek', lift_uuid, referee:ref, origin:org, find}
      }, null, e=>this.dbError(dmsg,e))
    },

    seek: function(msg) {			//DB now seeks to transmit this message
log.debug("Local seek:", msg)
      let { target, outc, topc, object, sequence, topt } = msg
        , pmsg = {target, action:'query', to:outc, from:topc, tally:topt, object}
        , dmsg = {target, sequence, object}
//log.debug("  pmsg:", JSON.stringify(pmsg,null,2))
      this.peerTransmit(pmsg, ()=>{		//Action: query
        this.dbProcess(msg, {
          context:	['init.seek'],
          update:	{status: 'seek'}
        }, null, e=>this.dbError(dmsg,e))
      }, e=>this.peerError(pmsg,e))
    },

    relay: function(msg) {			//the lift needs to be passed along
log.debug("Local relay:", JSON.stringify(msg, null))
      let { target, outc, topc, object, sequence, topt } = msg
        , pmsg = {target, action:'query', to:outc, from:topc, tally:topt, object}
        , dmsg = {target, sequence, object}
      this.peerTransmit(pmsg, ()=>{		//Action: 
        this.dbProcess(msg, {
          context:	['draft.relay'],
          update:	{status: 'pend'}
        }, null, e=>this.dbError(msg,e))
      }, e=>this.peerError(pmsg,e))
    },

    found: function(msg) {			//Lift destination found locally
log.debug("Local found:", JSON.stringify(msg, null))
      let { target, object, sequence, bott } = msg
        , { org, ref, find } = object
        , { plan, agent, host, port } = org
        , plain = decrypt(plan)
        , dmsg = {target, tally:bott, sequence, object}
//log.debug("  plain:", plain)
//log.debug("  dmsg:", JSON.stringify(dmsg, null))
      this.dbProcess(dmsg, {
        loop:		plain,
        context:	['draft.found'],
        update:		{status: 'found', request: 'term'}
      }, null, e=>this.dbError(dmsg,e))
    },

    term: function(msg) {			//Terminus node, notify sender
log.debug("Local term:", JSON.stringify(msg, null))
      let { target, action, outc, topc, object, sequence, topt } = msg
        , pmsg = {target, action, to:outc, from:topc, tally:topt, object}
        , dmsg = {target, sequence, object}
      this.peerTransmit(pmsg, ()=>{		//Action: 
        this.dbProcess(dmsg, {
          context:	['found.term'],
          update:	{status: 'pend'}
        }, null, e=>this.dbError(dmsg,e))
      }, e=>this.peerError(pmsg,e))
    },

    call: function(msg) {			//Need to get referee signature
log.debug("Local call:", JSON.stringify(msg, null))
      let { target, action, inpc, botc, object, sequence, bott } = msg
        , signature = 'Valid'
        , pmsg = {target, action: 'good', to:inpc, from:botc, tally:bott, object}
        , dmsg = {target, sequence, object}
      object.signed = signature
//log.debug("  pmsg:", JSON.stringify(pmsg, null))
      this.peerTransmit(pmsg, ()=>{		//Action: 
        this.dbProcess(dmsg, {
          context:	['seek.call'],
          update:	{status: 'good', signature}
        }, null, e=>this.dbError(dmsg,e))
      }, e=>this.peerError(pmsg,e))
    },

    void: function(msg) {			//We are voiding this lift (presumably with a ref signature)
log.debug("Local void:", JSON.stringify(msg, null))
      let { target, action, inpc, botc, object, sequence, bott } = msg
        , signature = 'Void'
        , pmsg = {target, action: 'void', to:inpc, from:botc, tally:bott, object}
        , dmsg = {target, sequence, object}
      object.signed = signature
//log.debug("  pmsg:", JSON.stringify(pmsg, null))
      this.peerTransmit(pmsg, ()=>{		//Action: 
        this.dbProcess(dmsg, {
          context: ['seek.void', 'seek.call','call.void','pend.void'],
          update:  {status: 'void', signature}
        }, null, e=>this.dbError(dmsg,e))
      }, e=>this.peerError(pmsg,e))
    },
  },

  remote: {					//Actions caused by a received peer packet
    query: function(msg) {		//A downstream peer server has asked to initiate a lift
log.debug("Remote lift query:", JSON.stringify(msg))
      this.dbProcess(msg, {
        query:	true
      }, null, e=>this.dbError(msg,e))
    },

    term: function(msg) {			//Response from lift destination
log.debug("Remote term:", JSON.stringify(msg, null))
      this.dbProcess(msg, {
        context: ['seek', 'seek.check'],
        update: {request: 'call'}		//Need to request signature
      }, null, e=>this.dbError(msg,e))
    },

    good: function(msg) {			//Got a valid return message from upstream
log.debug("Remote good:", JSON.stringify(msg, null))
      let {object} = msg
        , {signature} = object
//Fixme: Do validity checking on the message/signature
      this.dbProcess(msg, {
        context: ['seek', 'seek.check', 'seek.call', 'call', 'call.call', 'pend', 'pend.check'],
        update: {status: 'good', signature}
      }, null, e=>this.dbError(msg,e))
    },

    void: function(msg) {			//The upstream partner supplies a void signature
log.debug("Remote void:", JSON.stringify(msg, null))
      this.dbProcess(msg, {
        context: ['seek', 'seek.call','call','call.call', 'pend', 'pend.check'],
        update: {request: 'void'}
      }, null, e=>this.dbError(msg,e))
    },
  }
}

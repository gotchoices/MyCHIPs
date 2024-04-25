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
const ChipNet = require('chipnet')
const ChipCrypt = require('chipcrypt')
const ChipCode = require('chipcode')
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

module.exports = function() {
  this.local_init = async function(msg, pm) {		//A draft lift record has been created locally
log.debug("Local init:", JSON.stringify(msg))
    let { target, topc, object, sequence, init } = msg	//Grab message components
      , { org, ref, find, circuit } = init		//With default values for org,ref,find
      , lift_uuid = mkUuid(org?.cid, org?.agent)	//Permanent uuid
      , dmsg = {target, sequence, object}		//Make minimal return message for DB
log.debug(" init:", JSON.stringify(msg.init))
//    org.plan = encrypt(org.plan, find.agent)	//For recipient's eye's only
//log.debug("  dmsg:", JSON.stringify(dmsg, null, 2))

log.debug("Find:", find, pm.agent)
    if (find.agent == pm.agent) {		//Attempt a local lift
      pm.dbProcess(dmsg, {			//Update DB with origin, referee, find
        local:		true,			//Try a local lift
        context:	['draft.init'],		//Otherwise
        update:	{status: 'init', request: 'exec', lift_uuid, referee:ref, origin:org, find}
      }, null, e=>pm.dbError(dmsg,e))

    } else {					//Attempt a distributed lift
      const { cid, agent } = find
      const { units } = object
      const payeeAddress = {key: agent, identity: cid}
      const sql = `select inp_cid,inp,ath,out_cid,min,max,top_uuid,uuids
                   from mychips.tallies_v_paths where inp = $1 and foro`
      const parms = [msg.orig]			;log.debug("LI sql:", sql, 'parms:', parms)

      try {
        let queryRes = await pm.db.query(sql, parms)
log.debug("LI res:", queryRes)
        const iAmARef = false
        const version = 1
        const otherRefs = undefined
        const peerNodeLinks = (queryRes?.rows ?? []).map(row => {
          let max = row.max
          let min = row.min
          return {
            id: row.top_uuid,
            intents: [
              {code:'C', terms: {}, version},
              {code:'L', terms: {min, max}, version},
            ]
          }
        })
log.debug("LI links:", JSON.stringify(peerNodeLinks))
        const peerAddresses = []		//peer addresses, leave empty for now
        const asymmetric = new ChipCrypt.AsymmetricImpl()
        const keyPair = await asymmetric.generateKeyPairBin()
log.debug("LI pair:", Buffer.from(keyPair.publicKey).toString('base64'))
        const asymmetricVault = new ChipCrypt.AsymmetricVaultImpl(asymmetric, keyPair)
        const codeOptions = new ChipCode.CodeOptions()
        const cryptoHash = new ChipCode.CryptoHashImpl(codeOptions)
        const selfAddress = {key: pm.publicKey}
log.debug("LI self:", JSON.stringify(selfAddress))
        const participantState = new ChipNet.MemoryUniParticipantState(cryptoHash, peerNodeLinks, peerAddresses, selfAddress)

        const participantOptions = new ChipNet.UniParticipantOptions((request, linkID) => {
          //Call back here to transmit to the peer
log.debug("LI noise CB:", request, linkID)
//          pm.peerTransmit(pmsg, ()=>{		//Action: ?
//          }, e=>pm.peerError(pmsg,e))
        }, iAmARef, otherRefs, (linkIntent, queryIntents) => {		//Callback to do what???
log.debug("LI intent CB:", linkIntent, queryIntents)
          return [linkIntent]
        })
        const participant = new ChipNet.UniParticipant(
          participantOptions, participantState, asymmetric, cryptoHash
        )
        const originatorOptions = new ChipNet.UniOriginatorOptions()
        const originatorState = await ChipNet.MemoryUniOriginatorState.build(
          originatorOptions, peerNodeLinks, asymmetricVault, cryptoHash, {address: payeeAddress},
          [{code: 'L', terms: {min: units, max: units}, version}]
        )
        const originator = new ChipNet.UniOriginator(originatorState, participant)
log.debug("A")
        const plans = await originator.discover()
log.debug("LI plans:", plans)
        if (plans.length) {
          //Advance DB internal state to ??
        }

      } catch (err) {
  log.error('Initializing ChipNet: ' + err.stack)
      }
    } //if
  }

//For now, just fail all external lift requests
  this.local_exec = function(msg, pm) {		//Execute the lift remotely
log.debug("Local exec:", msg)
    let { org, ref, find, circuit } = msg.init	//With default values for org,ref,find
      , { target, topc, object, sequence } = msg	//Grab message components
      , lift_uuid = mkUuid(org?.cid, org?.agent)	//Permanent uuid
      , dmsg = {target, sequence, object}		//Make minimal return message for DB
    pm.dbProcess(dmsg, {			//Update DB with origin, referee, find
      context:	['init.exec'],
      update:		{status: 'void'}
    }, null, e=>pm.dbError(dmsg,e))
  }

//Obsolete?
  this.local_seek = function(msg, pm) {		//DB now seeks to transmit this message
log.debug("Local seek:", msg)
    let { target, outc, topc, object, sequence, topt } = msg
      , pmsg = {target, action:'query', to:outc, from:topc, tally:topt, object}
      , dmsg = {target, sequence, object}
//log.debug("  pmsg:", JSON.stringify(pmsg,null,2))
    pm.peerTransmit(pmsg, ()=>{		//Action: query
      pm.dbProcess(msg, {
        context:	['init.seek'],
        update:	{status: 'seek'}
      }, null, e=>pm.dbError(dmsg,e))
    }, e=>pm.peerError(pmsg,e))
  }

//Obsolete?
  this.local_relay = function(msg, pm) {	//the lift needs to be passed along
log.debug("Local relay:", JSON.stringify(msg, null))
    let { target, outc, topc, object, sequence, topt } = msg
      , pmsg = {target, action:'query', to:outc, from:topc, tally:topt, object}
      , dmsg = {target, sequence, object}
    pm.peerTransmit(pmsg, ()=>{		//Action: 
      pm.dbProcess(msg, {
        context:	['draft.relay'],
        update:	{status: 'pend'}
      }, null, e=>pm.dbError(msg,e))
    }, e=>pm.peerError(pmsg,e))
  }

//Obsolete?
  this.local_found = function(msg, pm) {	//Lift destination found locally
log.debug("Local found:", JSON.stringify(msg, null))
    let { target, object, sequence, bott } = msg
      , { org, ref, find } = object
      , { plan, agent, host, port } = org
      , plain = decrypt(plan)
      , dmsg = {target, tally:bott, sequence, object}
//log.debug("  plain:", plain)
//log.debug("  dmsg:", JSON.stringify(dmsg, null))
    pm.dbProcess(dmsg, {
      loop:		plain,
      context:	['draft.found'],
      update:		{status: 'found', request: 'term'}
    }, null, e=>pm.dbError(dmsg,e))
  }

//Obsolete?
  this.local_term = function(msg, pm) {		//Terminus node, notify sender
log.debug("Local term:", JSON.stringify(msg, null))
    let { target, action, outc, topc, object, sequence, topt } = msg
      , pmsg = {target, action, to:outc, from:topc, tally:topt, object}
      , dmsg = {target, sequence, object}
    pm.peerTransmit(pmsg, ()=>{		//Action: 
      pm.dbProcess(dmsg, {
        context:	['found.term'],
        update:	{status: 'pend'}
      }, null, e=>pm.dbError(dmsg,e))
    }, e=>pm.peerError(pmsg,e))
  }

//Obsolete?
  this.local_call = function(msg, pm) {		//Need to get referee signature
log.debug("Local call:", JSON.stringify(msg, null))
    let { target, action, inpc, botc, object, sequence, bott } = msg
      , signature = 'Valid'
      , pmsg = {target, action: 'good', to:inpc, from:botc, tally:bott, object}
      , dmsg = {target, sequence, object}
    object.signed = signature
//log.debug("  pmsg:", JSON.stringify(pmsg, null))
    pm.peerTransmit(pmsg, ()=>{		//Action: 
      pm.dbProcess(dmsg, {
        context:	['seek.call'],
        update:	{status: 'good', signature}
      }, null, e=>pm.dbError(dmsg,e))
    }, e=>pm.peerError(pmsg,e))
  }

//Obsolete?
  this.local_void = function(msg, pm) {		//We are voiding this lift (presumably with a ref signature)
log.debug("Local void:", JSON.stringify(msg, null))
    let { target, action, inpc, botc, object, sequence, bott } = msg
      , signature = 'Void'
      , pmsg = {target, action: 'void', to:inpc, from:botc, tally:bott, object}
      , dmsg = {target, sequence, object}
    object.signed = signature
//log.debug("  pmsg:", JSON.stringify(pmsg, null))
    pm.peerTransmit(pmsg, ()=>{		//Action: 
      pm.dbProcess(dmsg, {
        context: ['seek.void', 'seek.call','call.void','pend.void'],
        update:  {status: 'void', signature}
      }, null, e=>pm.dbError(dmsg,e))
    }, e=>pm.peerError(pmsg,e))
  }

//Obsolete?
  this.remote_query = function(msg, pm) {	//A downstream peer server has asked to initiate a lift
log.debug("Remote lift query:", JSON.stringify(msg))
    pm.dbProcess(msg, {
      query:	true
    }, null, e=>pm.dbError(msg,e))
  }

  this.remote_term = function(msg, pm) {	//Response from lift destination
log.debug("Remote term:", JSON.stringify(msg, null))
    pm.dbProcess(msg, {
      context: ['seek', 'seek.check'],
      update: {request: 'call'}		//Need to request signature
    }, null, e=>pm.dbError(msg,e))
  }

//Obsolete?
  this.remote_good = function(msg, pm) {	//Got a valid return message from upstream
log.debug("Remote good:", JSON.stringify(msg, null))
    let {object} = msg
      , {signature} = object
//Fixme: Do validity checking on the message/signature
    pm.dbProcess(msg, {
      context: ['seek', 'seek.check', 'seek.call', 'call', 'call.call', 'pend', 'pend.check'],
      update: {status: 'good', signature}
    }, null, e=>pm.dbError(msg,e))
  }

//Obsolete?
  this.remote_void = function(msg, pm) {	//The upstream partner supplies a void signature
log.debug("Remote void:", JSON.stringify(msg, null))
    pm.dbProcess(msg, {
      context: ['seek', 'seek.call','call','call.call', 'pend', 'pend.check'],
      update: {request: 'void'}
    }, null, e=>pm.dbError(msg,e))
  }
}

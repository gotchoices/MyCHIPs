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

const mkUuid = function(cuid, agent, mix = 'x') {
  let chad = 'chip://' + cuid + ':' + agent
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

module.exports = function(pm) {
  this.pm = pm

  this.participants = {};		//Cache of participants by "<cuid>:<agent>"
  this.getParticipant = async function(self, where, parms, version = 1) {
    const participantKey = `${self.cuid}:${self.agent}`
    if (Object.hasOwn(this.participants, participantKey)) return this.participants[participantKey];

    const codeOptions = new ChipCode.CodeOptions()
    const cryptoHash = new ChipCode.CryptoHashImpl(codeOptions)
    let chadMap = {}      //Remember to/from addresses by tally

    const getPeerState = async () => {
      const sql = `select inp_cid,inp,ath,out_chad,top_chad,min,max,top_uuid,uuids from mychips.tallies_v_paths where ${where}`
      const queryRes = await pm.db.query(sql, parms)	//Ask the DB for possible paths
      chadMap = {}			//Build/rebuild to/from addresses by tally
      const peerAddresses = []		//peer addresses, leave empty for now
      const selfAddress = {key: self.agent, identity: self.cuid}
      const peerNodeLinks = (queryRes?.rows ?? []).map(row => {
        chadMap[row.top_uuid] = {to: row.out_chad, from: row.top_chad, tally: row.top_uuid}
        return {
          id: row.top_uuid,
          intents: [
            {code:'C', terms: {}, version},
            {code:'L', terms: {min: row.min, max: row.max}, version},
          ],
        }
      })
      return new ChipNet.MemoryPeerState(cryptoHash, peerNodeLinks, peerAddresses, selfAddress)
    };
log.debug("LQ links:", JSON.stringify(peerNodeLinks))
    const asymmetric = new ChipCrypt.AsymmetricImpl()
    const keyPair = await asymmetric.generateKeyPairBin()
//log.debug("LQ pair:", Buffer.from(keyPair.publicKey).toString('base64'))
    const asymmetricVault = new ChipCrypt.AsymmetricVaultImpl(asymmetric, keyPair)
log.debug("LQ self:", JSON.stringify(selfAddress))
    const participantState = new ChipNet.MemoryUniParticipantState(cryptoHash)
  
    const participantOptions = new ChipNet.UniParticipantOptions(
      (request, linkID) => {			// queryPeer - callback to transmit query to the peer
log.debug("LQ noise CB:", request, linkID)
        const { to, from, tally } = chadMap[linkID];
        const pmsg = {target: 'lift', action:'query', to, from, tally, request}	//;log.debug("LQ packet send::", JSON.stringify(pmsg))
          
        return this.requester.request(pmsg)		//Return promise that remembers request context
      }, 
      true,   // we want to be a referee
      (linkIntent, queryIntents) => {		// Negotiate intent
log.debug("LQ intent CB:", linkIntent, queryIntents)
        // TODO: Reduce the min/max of lift intent to be lesser of the two
        return linkIntent
      },
      undefined,		// Self secret
      undefined,    // Other members 
    )
  
    const participant = new ChipNet.UniParticipant(
      participantOptions, participantState, asymmetricVault, cryptoHash, getPeerState
    )
    this.participants[participantKey] = participant;
    return participant;
  }

  this.requester = new ChipNet.Requester(message => {
//log.debug("L requester:", JSON.stringify(message))
    const pmsg = {...message.body, request: {messageId: message.messageId, body:message.body.request}}
    this.pm.peerTransmit(pmsg, ()=>{
//log.debug("L req pmsg sent:", this.pm.agent, '->', pmsg.to.agent)
    }, e=>pm.peerError(pmsg,e))
  })

  this.local_init = async function(msg, pm) {		//A draft lift record has been created locally
log.debug("Local init:", JSON.stringify(msg))
    let { target, object, sequence, init, orig } = msg	//Grab message components
      , { org } = object
      , { auth, find, ref } = init

log.debug("LI find:", find, pm.agent)
    if (find.agent == pm.agent) {		//Attempt a local lift
      try {
        let lift_uuid = mkUuid(org?.cuid, org?.agent)	//Permanent uuid
        , dmsg = {target, sequence, object}		//Make minimal return message for DB
        pm.dbProcess(dmsg, {			//Update DB with origin, referee, find
          local:		true,			//Try a local lift
          context:	['draft.init'],		//Otherwise
          update:	{status: 'init', request: 'exec', lift_uuid, referee:ref, origin:org, find}
        }, null, e=>pm.dbError(dmsg,e))
      } catch (err) {
          log.error('Initializing local lift: ' + err.message)
      }

    } else {					//Attempt a distributed lift via chipNet
      const { cuid, agent } = find
      const { units } = object

      try {
        const where = 'inp = $1 and foro'
        const parms = [msg.orig]

        const participant = await this.getParticipant(org, where, parms)
log.debug("LI partic:", participant)
        
        const originatorOptions = new ChipNet.UniOriginatorOptions();
        originatorOptions.debugBudget = 30000;
        const address = {key: agent, identity: cuid}
        const originatorState = await ChipNet.MemoryUniOriginatorState.build(
          originatorOptions, 
          participant.state.peerLinks,
          participant.asymmetricVault,
          participant.cryptoHash,
          {address},
          [{code: 'L', terms: {min: units, max: units}, version}]
        )
        const originator = new ChipNet.UniOriginator(originatorState, participant)
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
      , lift_uuid = mkUuid(org?.cuid, org?.agent)	//Permanent uuid
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
//  this.remote_query = function(msg, pm) {	//A downstream peer server has asked to initiate a lift
//log.debug("Remote lift query:", JSON.stringify(msg))
//    pm.dbProcess(msg, {
//      query:	true
//    }, null, e=>pm.dbError(msg,e))
//  }

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

  this.remote_query = async function(msg, pm) {	//Peer responding to discovery query
    const {to, from, target, tally} = msg
log.debug("Remote query:", this.pm.agent, msg)

    try {
      const responder = new ChipNet.Responder(message => {	//send callback
log.debug("L responder:", JSON.stringify(message))
        const pmsg = {to: from, from: to, target, action: 'resp',
          request: {messageId: message.messageId, body:message.body}
        }
        this.pm.peerTransmit(pmsg, ()=>{
log.debug("L resp pmsg sent:", this.pm.agent, '->', pmsg.to.agent)
         }, e=>pm.peerError(pmsg,e))
      }, async (body) => {		//Process
  
log.debug("L resp process:", this.pm.agent, JSON.stringify(body))
        const where = 'inp_cid = $1 and inp_agent = $2 and foro'
        const parms = [to.cuid, to.agent]
        const participant = await this.getParticipant(to, where, parms)
        const queryResult = await participant.query(body, tally);
        return queryResult;
      })
  
      await responder.request(msg.request)
    } catch(err) {
      log.error("In remote query:", err.stack)
    }
  }
  
  this.remote_resp = function(msg, pm) {	//Peer responding to discovery query
    try {
      this.requester.response(msg.request)
    } catch(err) {
      log.error("In remote response:", err.stack)
    }
  }
  
}

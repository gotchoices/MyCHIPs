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
const SubCrypto = require('./subcrypto.js')
const subCrypto = new SubCrypto(log)
const NoiseCrypto = require('./gencrypto.js')
const noiseCrypto = new NoiseCrypto(log)

//const Stringify = require('json-stable-stringify')
//const Hash = require('hash.js')

const mkUuid = function(cuid, agent, mix = 'x') {
  let chad = 'chip://' + cuid + ':' + agent
    , date = new Date().toISOString()
    , uuid = Uuid.v5(date+mix, Uuid.v5(chad, Uuid.v5.URL))
  return uuid
}

//const encrypt = function(obj, agent) {		//Fixme: insert actual noise encryption here
//  return Buffer.from(JSON.stringify(obj)).toString('base64url')
//}
//const decrypt = function(str) {		//Fixme: insert actual noise decryption here
//  let plain = Buffer.from(str, 'base64url').toString()
//    , obj = JSON.parse(plain)
//  return obj
//}

module.exports = function(pm) {
  this.pm = pm

  this.participants = {};		//Cache of participants by "<cuid>:<agent>"
  this.getParticipant = async function(self, pathSpec) {
    const participantKey = `${self.cuid}:${self.agent}`		//;log.debug("Lgp pk:", participantKey)
    if (Object.hasOwn(this.participants, participantKey))
      return this.participants[participantKey]

    const codeOptions = new ChipCode.CodeOptions()
    const cryptoHash = new ChipCode.CryptoHashImpl(codeOptions)
    let chadMap = {}	//Remember to/from addresses by tally
    let peerState	//Will cache value when called

    const getPeerState = async () => {
      let {where, parms, rows} = pathSpec
      if (!rows) {			//We must query DB
        const sql = `select out_chad,top_chad,min,max,top_uuid from mychips.tallies_v_paths where ${where}`
        const queryRes = await pm.db.query(sql, parms)	//Ask the DB for possible paths
        rows = queryRes?.rows
      }					//;log.debug("LQ gps rows:", JSON.stringify(rows))
      chadMap = {}			//Build/rebuild to/from addresses by tally
      const peerAddresses = []		//peer addresses, leave empty for now
      const selfAddress = {key: self.agent, identity: self.cuid}
      const peerNodeLinks = (rows ?? []).map(row => {
        chadMap[row.top_uuid] = {to: row.out_chad, from: row.top_chad, tally: row.top_uuid}
        return {
          id: row.top_uuid,
          intents: {
            'C': {},
            'L': {min: row.min, max: row.max}
          }
        }
      })
//log.debug("LQ links:", JSON.stringify(peerNodeLinks))
      peerState = new ChipNet.MemoryPeerState(cryptoHash, peerNodeLinks, peerAddresses, selfAddress)
      return peerState
    }

    try {
      const asymmetric = new ChipCrypt.AsymmetricImpl()
      const keyPair = await asymmetric.generateKeyPairBin()
//log.debug("LQ pair:", Buffer.from(keyPair.publicKey).toString('base64'))
      const asymmetricVault = new ChipCrypt.AsymmetricVaultImpl(asymmetric, keyPair)
//log.debug("LQ vault:", asymmetricVault)
      const participantState = new ChipNet.MemoryUniParticipantState(cryptoHash)
  
      const participantOptions = new ChipNet.UniParticipantOptions(
        (request, linkID) => {			// queryPeer - callback to transmit query to the peer
//log.debug("LQ noise CB:", request, linkID)
          const { to, from, tally } = chadMap[linkID];
          const pmsg = {target: 'lift', action:'query', to, from, tally, request}	//;log.debug("LQ packet send::", JSON.stringify(pmsg))
          
          return this.requester.request(pmsg)		//Return promise that remembers request context
        }, 
        true,   // we want to be a referee
        (linkIntent, queryIntents) => {		// Negotiate intent
//log.debug("LQ intent CB:", linkIntent, queryIntents)
          // TODO: Reduce the min/max of lift intent to be lesser of the two
          return linkIntent
        },
        undefined,		// Self secret
        undefined,    // Other members 
      )
  
      const participant = new ChipNet.UniParticipant(
        participantOptions, participantState, asymmetricVault, cryptoHash, getPeerState,
        (queryTerms, planTerms) => {		//log.debug('Terms Check:', JSON.stringify(queryTerms), JSON.stringify(planTerms))
          return (queryTerms.units <= planTerms.min)
        }
      )
      const result = {participant, getPeerState: () => peerState}
      this.participants[participantKey] = result
      return result
    } catch (err) {
      log.error("Initializing participant", err.message)
      throw err
    }
  }

  this.requester = new ChipNet.Requester(message => {
//log.debug("L requester:", JSON.stringify(message))
    const pmsg = {...message.body, request: {messageId: message.messageId, body:message.body.request}}
    this.pm.peerTransmit(pmsg, ()=>{
//log.debug("L req pmsg sent:", this.pm.agent, '->', pmsg.to.agent)
    }, e=>pm.peerError(pmsg,e))
  })

  this.local_init = async function(msg, pm) {		//New lift has been drafted locally
log.debug("Local init:", msg)
    const { target, object, sequence, init } = msg	//Grab message components
        , { org, find } = object
        , { pub, core, auth } = init
        , dmsg = {target, sequence, object}		//Make minimal return message for DB
//log.debug("LI PV:", pub, auth.sign, 'c:', core)
    isValid = await subCrypto.verify(pub, core, auth.sign)	//Check user's signature
    let recipe = {context: ['draft.init']}		//;log.debug("LI isValid:", isValid)
    if (isValid) {					//;log.debug("LI AV:", pm.keys.publicKey, 'o:', object)
//log.debug("LI PK:", pm.keys.publicKey)
      let agent = noiseCrypto.sign(pm.keys.privateKey, object)	//;log.debug("LI ASs:", agent)
      recipe.update = {status: 'init', request: 'seek', agent_auth: {agent}}
      recipe.route = true				//Check routes for local/external
      pm.dbProcess(dmsg, recipe, null, e=>pm.dbError(dmsg,e))
    } else {
      recipe.update = {status: 'void'}
      pm.dbProcess(dmsg, recipe, null, e=>pm.dbError(dmsg,e))
    }
  }

  this.local_seek = async function(msg, pm) {		//A draft lift record has been created locally
log.debug("Local seek:", msg)
    const { target, object, sequence, seek } = msg	//Grab message components
        , { find, units } = object
        , { cuid, agent } = find			//;log.debug("LS find:", find, 'me:', pm.agent)
        , { paths, origin } = seek			//;log.debug("LS seek:", origin, 'p:', paths)
        , dmsg = {target, sequence, object}		//Make minimal return message for DB
    try {
//log.debug("LS o:", origin, 'p:', paths, 'u:', units)

      const { participant, getPeerState } = await this.getParticipant(origin, {rows: paths})
        
      const originatorOptions = new ChipNet.UniOriginatorOptions()
      originatorOptions.debugBudget = 30000
      const address = {key: agent, identity: cuid}
      const originatorState = await ChipNet.MemoryUniOriginatorState.build(
        originatorOptions, 
        participant.state.peerLinks
      )
      const originator = new ChipNet.UniOriginator(originatorState, participant, participant.cryptoHash, participant.assymetricVault)
      const { plans, sessionCode } = await originator.discover(
        {address}, 
        {'L': {units}}
      )
      const peerState = getPeerState()		//;log.debug("LS plans:", JSON.stringify(plans))
      const edgeMapper = await peerState.getPeerLinksByNonce(sessionCode)
      const mapPlans = plans.map(plan => {
        const nonce0 = plan.path[0].nonce
        const via = edgeMapper[nonce0]		//;log.debug('LS nv0', nonce0, 'v:', via)
        return { ...plan, via }
      })					//;log.debug("LS mapPlans:", JSON.stringify(mapPlans))
log.debug("LS mapPlans:", JSON.stringify(mapPlans))
      let recipe = {context: ['init.seek']}
      if (mapPlans.length) {        // Discovery succeeded
        recipe.pick = true			//Pick optimal lift route(s)
        recipe.update = {status: 'seek', request: 'exec', transact: mapPlans}
        pm.dbProcess(dmsg, recipe, null, e=>pm.dbError(dmsg,e))
      } else {		        // Discovery failed, no plans found
        recipe.update = {status: 'void'}
        pm.dbProcess(dmsg, recipe, null, e=>pm.dbError(dmsg,e))
      }

    } catch (err) {
      log.error('Initializing ChipNet: ' + err.stack)
    }
  }

//For now, just fail all external lift requests
  this.local_exec = function(msg, pm) {		//Execute the lift remotely
log.debug("Local exec:", msg)
//    let { org, ref, find, circuit } = msg.init	//With default values for org,ref,find
//      , { target, topc, object, sequence } = msg	//Grab message components
//      , lift_uuid = mkUuid(org?.cuid, org?.agent)	//Permanent uuid
//      , dmsg = {target, sequence, object}		//Make minimal return message for DB
//    pm.dbProcess(dmsg, {			//Update DB with origin, referee, find
//      context:	['init.exec'],
//      update:		{status: 'void'}
//    }, null, e=>pm.dbError(dmsg,e))
  }

  this.remote_query = async function(msg, pm) {	//Peer responding to discovery query
    const {to, from, target, tally} = msg
//log.debug("Remote query:", from.agent, from.cuid, '->', to.agent, to.cuid)

    try {
      const responder = new ChipNet.Responder(message => {	//send callback
//log.debug("L responder:", JSON.stringify(message))
        const pmsg = {to: from, from: to, target, action: 'resp',
          request: {messageId: message.messageId, body:message.body}
        }
        this.pm.peerTransmit(pmsg, ()=>{
//log.debug("L resp pmsg sent:", this.pm.agent, '->', pmsg.to.agent)
         }, e=>pm.peerError(pmsg,e))
      }, async (body) => {		//Process response to a query

try {  	//DEBUG only
//log.debug("L resp process:", this.pm.agent, JSON.stringify(body))
          const where = 'inp_cuid = $1 and inp_agent = $2 and foro'
          const parms = [to.cuid, to.agent]
          const { participant } = await this.getParticipant(to, {where, parms})
          const queryResult = await participant.query(body, tally);
          return queryResult;
  
} catch(e) {
  log.error("Lift error in query response:", e)
  throw e
}
      })

      await responder.request(msg.request)
    } catch(err) {
      log.error("In lift remote_query:", err.stack)
    }
  }
  
  this.remote_resp = function(msg, pm) {	//Peer responding to discovery query
//log.debug("lift remote resp:", this.pm.agent, msg.from, '->', msg.to)
    try {
      this.requester.response(msg.request)
    } catch(err) {
      log.error("In remote response:", err.stack)
    }
  }
  
}

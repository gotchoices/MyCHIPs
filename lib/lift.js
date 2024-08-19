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
const ChipNetUni = require('chipnet/unidirectional')
const ChipCrypt = require('chipcrypt')
const ChipCode = require('chipcode')
const SubCrypto = require('./subcrypto.js')
const subCrypto = new SubCrypto(log)
const NoiseCrypto = require('./gencrypto.js')
const noiseCrypto = new NoiseCrypto(log)

const mkUuid = function(cuid, agent, mix = 'x') {
  let chad = 'chip://' + cuid + ':' + agent
    , date = new Date().toISOString()
    , uuid = Uuid.v5(date+mix, Uuid.v5(chad, Uuid.v5.URL))
  return uuid
}

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

    try {
      const asymmetric = new ChipCrypt.AsymmetricImpl()
      const keyPair = await asymmetric.generateKeyPairBin()
//log.debug("LQ pair:", Buffer.from(keyPair.publicKey).toString('base64'))
      const asymmetricVault = new ChipCrypt.AsymmetricVaultImpl(asymmetric, keyPair)
//log.debug("LQ vault:", asymmetricVault)
      const participantState = new ChipNetUni.MemoryUniParticipantState(cryptoHash)
  
      const participantOptions = new ChipNetUni.UniParticipantOptions(
        (linkIntent, queryIntents) => {		// Negotiate intent
//log.debug("LQ intent CB:", linkIntent, queryIntents)
          // TODO: Reduce the min/max of lift intent to be lesser of the two
          return linkIntent
        }
      )
  
      const findAddress =   //See what paths we have to offer ChipNet
        async (query) => {
          const { target, intents } = query
          const { units } = intents.L
          const { key, cuid } = target.address
          const parms = [self.cuid, units, cuid, key]
          const sql = "select fori,foro,bot,out,path,inp_cuid,out_cuid,top_uuid,min,max,out_chad,top_chad,out_agent from mychips.tallies_v_paths where inp_cuid = $1 and min >= $2 and (foro or (out_cuid = $3 and out_agent = $4))"
          const queryRes = await pm.db.query(sql, parms) //Ask the DB for possible paths
          rows = queryRes?.rows
log.debug("PQ Find:", this.pm.agent, sql, parms, rows.length)
//rows.forEach(r => { log.debug("  find:", r) })
          const selfMatchRow = rows.find(r => (!r.foro && r.out_agent == key && r.out_cuid == cuid))
          const selfIsMatch = Boolean(selfMatchRow)
          const peerRows = rows.find(r => (r.foro && r.out_agent == key && r.out_cuid == cuid))
          const candRows = rows.filter(r => (r.foro && (r.out_agent != key || r.out_cuid != cuid)))
          chadMap = Object.fromEntries(rows.map(r => [r.top_uuid, {to: r.out_chad, from: r.top_chad}]))
          const selfObj = {
            member: {
              address: selfIsMatch ? { key, cuid } : { key: self.agent, cuid: self.cuid },
              types: ['P', 'R'] //TODO: determine from DB if we are referee
            },
            //          dependsOn: TODO: can add external referees
          }
          const peerMatch = peerRows?.map(r => ({
            match: {
              member: {
                address: { key: r.agent, cuid: r.cuid },
                types: ['P', 'R'] //TODO: determine from DB if we are referee
              }
            },
            link: {
              id: r.top_uuid,
              intents: { 'L': { min: r.min, max: r.max } }
            }
          }))
          const candidates = candRows?.map(r => ({
            id: r.top_uuid,
            intents: { 'L': { min: r.min, max: r.max } }
          }))

log.debug("PQ ret:", JSON.stringify(selfObj), 'sm:', selfIsMatch, 'pm:', peerMatch, 'c:', JSON.stringify(candidates))
          return { self: selfObj, selfIsMatch, peerMatch, candidates }
        }

        const intentSatisfied = (queryTerms, planTerms) => {
        return (queryTerms.units <= planTerms.min)
      }

      const queryPeer = (request, linkID) => {  //chipNet requests we send packet to peer
//log.debug("LQ noise CB:", request, linkID)
        const { to, from } = chadMap[linkID]
        const pmsg = { target: 'lift', action: 'query', to, from, tally: linkID, request }
log.debug("LQ packet send:", this.pm.agent, from.cuid, '->', to.cuid, linkID)
        return this.requester.request(pmsg)
      }
      const participant = new ChipNetUni.UniParticipant(
        participantOptions, participantState, asymmetricVault, cryptoHash, findAddress,intentSatisfied, queryPeer
      )
      const result = {participant, participantState}
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
    const { target, object, sequence, aux } = msg	//Grab message components
        , { org, find } = object
        , { pub, core, auth } = aux
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
    const { target, object, sequence, aux } = msg	//Grab message components
        , { find, units } = object
        , { cuid, agent } = find			//;log.debug("LS find:", find, 'me:', pm.agent)
        , { trans, origin } = aux			//;log.debug("LS aux:", origin, 'p:', trans)
        , dmsg = {target, sequence, object}		//Make minimal return message for DB
    try {
//log.debug("LS o:", origin, 'p:', trans, 'u:', units)

      const { participant, participantState } = await this.getParticipant(origin, {rows: trans})
        
      const originatorOptions = new ChipNetUni.UniOriginatorOptions()
      originatorOptions.debugBudget = 30000
      const address = {key: agent, cuid}
      const originatorState = await ChipNetUni.MemoryUniOriginatorState.build(
        originatorOptions, 
        participant.state.peerLinks
      )
      const originator = new ChipNetUni.UniOriginator(originatorState, participant, participant.cryptoHash, participant.assymetricVault)
      const { plans, sessionCode } = await originator.discover(
        {address}, 
        {'L': {units}}
      )
//      const peerState = getPeerState()		//;log.debug("LS plans:", JSON.stringify(plans))
//      const edgeMapper = await peerState.getPeerLinksByNonce(sessionCode)
      const edgeMapper = (await participantState.getContext(sessionCode, [])).linkIdsByNonce
      const mapPlans = plans.map(plan => {
        const nonce0 = plan.path[0].nonce
        const via = edgeMapper[nonce0]
log.debug('LS nv0', nonce0, 'v:', via)
        return { ...plan, via }
      })					//;log.debug("LS mapPlans:", JSON.stringify(mapPlans))
log.debug("LS mapPlans:", JSON.stringify(mapPlans))
      let recipe = {context: ['init.seek']}
      if (mapPlans.length) {        // Discovery succeeded
        recipe.pick = true			//Pick optimal lift route(s)
        recipe.update = {status: 'seek', request: 'exec', transact: {plans: mapPlans}}
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
    const { target, object, sequence, aux } = msg	//Grab message components
//        , { find, units } = object
//        , { cuid, agent } = find			//;log.debug("LE find:", find, 'me:', pm.agent)
        , { trans, origin } = aux			;log.debug("LE aux:", origin, 'p:', trans)
        , { plans, pick } = trans			;log.debug("LE pick:", pick)

      , dmsg = {target, sequence, object}		//Make minimal return message for DB

//      const topology = buildTopology(paths, pick)
//      start_transaction(topology, () => {
//      pm.dbProcess(dmsg, {			//Update DB with origin, referee, find
//        context:	['seek.exec'],
//        update:	{status: 'exec'}
//      }, null, e=>pm.dbError(dmsg,e))
//      })

  }

  this.remote_query = async function(msg, pm) {	//Peer responding to discovery query
    const {to, from, target, tally} = msg
log.debug("Remote query:", from.agent, from.cuid, '->', to.agent, to.cuid)

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

try {  	//DEBUG
//log.debug("L resp process:", this.pm.agent, JSON.stringify(body))
          const where = 'inp_cuid = $1 and inp_agent = $2 and foro'
          const parms = [to.cuid, to.agent]
          const { participant } = await this.getParticipant(to, {where, parms})
          const queryResult = await participant.query(body, tally);
          return queryResult;
  
} catch(e) {  	//DEBUG
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

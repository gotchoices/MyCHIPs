//State machine map for distributed lift execution
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 
const { Log } = require('wyclif')
var log = Log('lift')
const Uuid = require('uuid')
const ChipNet = require('chipnet')
const ChipNetUni = require('chipnet/unidirectional')
const ChipNetTrx = require('chipnet/transaction')
const ChipCrypt = require('chipcrypt')
const ChipCode = require('chipcode')
const SubCrypto = require('./subcrypto.js')
const subCrypto = new SubCrypto(log)
const NoiseCrypto = require('./gencrypto.js')
const noiseCrypto = new NoiseCrypto(log)

module.exports = function(pm) {
  this.pm = pm

  // TODO: bound this cache by time and size
  this.discoParticipants = {};		// Cache of participants by "<cuid>:<agent>"

  this.getDiscoFromCache = function(participantKey) {
    if (Object.hasOwn(this.discoParticipants, participantKey))
      return this.discoParticipants[participantKey]
  }
  
  this.getDiscoParticipant = async function(self, pathSpec) {
    const participantKey = `${self.cuid}:${self.agent}`		//;log.debug("Lgp pk:", participantKey)
    let result = this.getDiscoFromCache(participantKey)
    if (result) return result

    const cryptoHash = new ChipCode.CryptoHashImpl()
     let chadMap = {}	//Remember to/from addresses by tally

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
        const peerRows = rows.filter(r => (r.foro && r.out_agent == key && r.out_cuid == cuid))
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
              address: { key: r.out_agent, cuid: r.out_cuid },
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
      const pmsg = { target: 'lift', action: 'disco', to, from, tally: linkID, request }
log.debug("LQ packet send:", this.pm.agent, from.cuid, '->', to.cuid, linkID)
      return this.requester.request(pmsg)
    }

    const participant = new ChipNetUni.UniParticipant(
      participantOptions, participantState, asymmetricVault, cryptoHash, findAddress,intentSatisfied, queryPeer
    )
    result = {participant, participantState}
    this.discoParticipants[participantKey] = result
    return result
  }   //getDiscoParticipant

  this.requester = new ChipNet.Requester(message => {
//log.debug("L requester:", message.body.from.cuid, '->', message.body.to.cuid)
    const pmsg = {...message.body, request: {messageId: message.messageId, body:message.body.request}}
    this.pm.peerTransmit(pmsg, ()=>{
//log.debug("L req pmsg sent:", this.pm.agent, '->', pmsg.to.agent)
    }, e=>pm.peerError(pmsg,e))
  })

  this.local_init = async function(msg, pm) {		//New lift has been drafted locally
log.debug("Local init:", msg)
    const { target, object, sequence, aux } = msg	//Grab message components
        , { org, find } = object
        , { pub, pay, auth } = aux
        , dmsg = {target, sequence, object}		//Make minimal return message for DB
//log.debug("LI PV:", pub, auth.sign, 'c:', pay)
    isValid = await subCrypto.verify(pub, pay, auth.sign)	//Check user's signature
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

      const { participant, participantState } = await this.getDiscoParticipant(origin, {rows: trans})
        
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
  }	//local_seek

  this.trxParticipants = {}

  this.getTrxParticipant = async function(self, getDmsg) {
    const participantKey = `${self.cuid}:${self.agent}`		//;log.debug("Lgp pk:", participantKey)
    if (Object.hasOwn(this.trxParticipants, participantKey))
      return this.trxParticipants[participantKey]

    const trxResources = {
      promise: async (member, inLink, outLink, record) => {
        const { nonce, link } = outLink ?? inLink
        const { intents } = link
        const units = intents.L.min
//        const inp = {agent: member.address.key, cuid: member.address.cuid}
//        const out = {agent: target.key, cuid: target.cuid}
        let inp, out, context, status, promise, insert = false;
        if (inLink && outLink) {   //intermediary
          inp = {agent: inLink.link?.target?.key, cuid: inLink.link?.target?.cuid}
          out = {agent: outLink.link?.target?.key, cuid: outLink.link?.target?.cuid}
          promise = {inp, out, units}
          context = ['null']
          status = 'part'
          insert = true
        } else if (inLink) {    //terminus
          inp = {agent: inLink.link?.source?.key, cuid: inLink.link?.source?.cuid}
          out = {agent: inLink.link?.target?.key, cuid: inLink.link?.target?.cuid}
          promise = {inp, out, units}
          context = ['null']
          status = 'part'
          insert = true
        } else if (outLink) {   //originator
          const participantKey = `${self.cuid}:${self.agent}`
          const { participantState } = this.getDiscoFromCache(participantKey)
          const edgeMapper = (await participantState.getContext(record.sessionCode, [])).linkIdsByNonce
          const via = edgeMapper[nonce]
//          inp = {agent: member.address.key, cuid: member.address.cuid}
          inp = {agent: outLink.link?.source?.key, cuid: outLink.link?.source?.cuid}
          out = {agent: outLink.link.target.key, cuid: outLink.link.target.cuid}
          promise = {inp, out, units, via}
          context = ['seek.exec']
          status = 'exec'
        }
        const recipe = {promise, context, update: {status}, insert}
        const dmsg = getDmsg()
log.debug("LE pr:", this.pm.agent, 'io:', !!inLink, !!outLink, 'ol:', JSON.stringify(outLink), 'dm:', JSON.stringify(dmsg))
        await new Promise(
          (resolve, reject) => pm.dbProcess(dmsg, recipe, resolve, e => {
              pm.dbError(dmsg, e)
              reject(e)
            }
          )
        )
      },
      release: async (isSuccess, member, inLink, outLink, record) => {
log.debug("LE rel:", this.pm.agent, member)
      },
    }
    const trxParticipantState = new ChipNetTrx.MemoryTrxParticipantState({
      address: {key: self.agent, cuid: self.cuid},
      types: ['P', 'R']
    })
    const asymmetric = new ChipCrypt.AsymmetricImpl()
    const keyPair = await asymmetric.generateKeyPairBin()
    const asymmetricVault = new ChipCrypt.AsymmetricVaultImpl(asymmetric, keyPair)
    const cryptoHash = new ChipCode.CryptoHashImpl()
    const trxParticipant = new ChipNetTrx.TrxParticipant (
      trxParticipantState,
      asymmetricVault,
      asymmetric,
      cryptoHash,
      async (address, record) => {    //updatePeer: ChipNet asking to send update to peer
        const { rows } = await pm.db.query('select agent_host, agent_port from mychips.agents where agent = $1', [address.key])
        const phys = rows[0]
        const to = {agent: address.key, cuid: address.cuid, host: phys.agent_host, port: phys.agent_port}
        const o = getDmsg().object
        const object = {lift: o.lift, date: o.date, life: o.life, units: o.units}    //Only send what next peer needs
        const pmsg = { target: 'lift', action: 'update', to, from: self, object, request: record }
log.debug("LE pT:", pmsg.from, '->', pmsg.to)
        return this.requester.request(pmsg)
      },
      trxResources
    )
    return trxParticipant
  }   //getTrxParticipant

  this.local_exec = async function(msg, pm) {		//Execute the lift remotely
log.debug("Local exec:", msg)
    const { target, object, sequence, aux } = msg	//Grab message components
    const { trans, origin } = aux			        //;log.debug("LE aux:", origin, 'p:', trans)
    const { plans, pick } = trans			        //;log.debug("LE pick:", pick)
    const dmsg = {target, sequence, object}		//Make minimal return message for DB
    const plan = plans[pick]
    const topology = {
      members: plan.members,
      links: Object.fromEntries(plan.path.map((edge, idx) => [edge.nonce, {
        source: plan.members[idx].address,
        target: plan.members[idx+1].address,
        intents: edge.intents
      }]))
    }
    const cryptoHash = new ChipCode.CryptoHashImpl({ageMs: object.life * 1000})
    const trxRecord = {
      transactionCode: await cryptoHash.generate(),
      sessionCode: plan.sessionCode,
      payload: {lift: object},
      topology,
      promises: [],
      commits: []
    }
    const trxParticipant = await this.getTrxParticipant(origin, () => dmsg);
log.debug("LE up:")
    trxParticipant.update(trxRecord)
  }	//local_exec

  this.remote_disco = async function(msg, pm) {	//Peer responding to discovery query
    const {to, from, target, tally} = msg
log.debug("Remote disco:", from.agent, from.cuid, '->', to.agent, to.cuid)

    const responder = new ChipNet.Responder(message => {	//send callback
//log.debug("L responder:", JSON.stringify(message))
      const pmsg = {to: from, from: to, target, action: 'disco_resp',
        request: {messageId: message.messageId, body:message.body}
      }
      this.pm.peerTransmit(pmsg, ()=>{
//log.debug("L resp pmsg sent:", this.pm.agent, '->', pmsg.to.agent)
        }, e=>pm.peerError(pmsg,e))
    }, async (body) => {		//Process response to a query

//log.debug("L resp process:", this.pm.agent, JSON.stringify(body))
        const where = 'inp_cuid = $1 and inp_agent = $2 and foro'
        const parms = [to.cuid, to.agent]
        const { participant } = await this.getDiscoParticipant(to, {where, parms})
        const queryResult = await participant.query(body, tally);
        return queryResult;
    })

    await responder.request(msg.request)
  }	//remote_disco
  
  this.remote_disco_resp = function(msg, pm) {	//Peer discovery response
//log.debug("lift remote resp:", this.pm.agent, msg.from, '->', msg.to)
    this.requester.response(msg.request)
  }
  
  this.remote_update = async function(msg, pm) {	//Peer sending us a lift transaction
    const {to, from, target, object} = msg
    const dmsg = {target, object}
log.debug("Remote update:", from.agent, from.cuid, '->', to.agent, to.cuid, msg)

    const responder = new ChipNet.Responder(message => {	//send callback
//log.debug("L trx responder:", JSON.stringify(message))
      const pmsg = {to: from, from: to, target, action: 'trx_resp',
        request: {messageId: message.messageId, body:message.body}
      }
      this.pm.peerTransmit(pmsg, ()=>{
//log.debug("L trx resp pmsg sent:", this.pm.agent, '->', pmsg.to.agent)
        }, e=>pm.peerError(pmsg,e))
    }, async (body) => {		//Process response to a query

//log.debug("L trx resp process:", this.pm.agent, JSON.stringify(body))
        const participant = await this.getTrxParticipant(to, () => dmsg)
        const peer = { key: from.agent, cuid: from.cuid };
        await participant.update(body, peer);
    })

    await responder.request(msg.request)
  }	//remote_update

  this.remote_trx_resp = function(msg, pm) {	//Peer responding to lift transaction
    //log.debug("remote update resp:", this.pm.agent, msg.from, '->', msg.to)
    this.requester.response(msg.request)
  }
}

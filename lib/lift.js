//Interface with ChipNet for distributed lift execution
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- Query DB on startup and periodically for stale, incomplete lifts, query peers for update on these
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
  
  this.addrCache = {}                     //Store physical addresses of known agents
  this.addrUpdate = function(addr) {      //Freshen address cache
    const { agent, host, port } = addr
    if (agent && host && port)
      this.addrCache[agent] = {host, port}
  }
  this.addrFetch = async function(addr) {       //Fill in agent, host, port in an address record
    let { key, agent, host, port } = addr
    let passedIn = {...addr}; delete passedIn.key
    if (key) {
      agent = key
    }
    const cached = this.addrCache[agent]
    if (cached) {
      host = cached.host
      port = cached.port
    } else if (agent) {
      const { rows } = await pm.db.query('select agent_host, agent_port from mychips.agents where agent = $1', [agent])
      const row = rows[0]
      host = row.agent_host
      port = row.agent_port
    }
    return {...passedIn, agent, host, port}
  }

  // TODO: bound this cache by time and size
  this.discoParticipants = {};		// Cache of discovery participants indexed by "agent"

  this.getDiscoFromCache = function(participantKey) {   //Fetch cached participant info
    if (Object.hasOwn(this.discoParticipants, participantKey))
      return this.discoParticipants[participantKey]
  }

  this.linkMapsBySession = {};		// Cache of tally uuids (linkIds) indexed by nonce, for each session

  this.requester = new ChipNet.Requester()    //ChipNet requires packet.request to contain a message ID, which this will handle
  
  this.getDiscoParticipant = async function(self) {     //Create participant instance for discovery
    const participantKey = `${self.cuid}:${self.agent}`		//;log.debug("Lgp pk:", participantKey)
    let result = this.getDiscoFromCache(participantKey)   //If we already have one, just use it
    if (result) return result

    let chadMap = {}            //Remember to/from addresses indexed by tally

    const cryptoHash = new ChipCode.CryptoHashImpl()    //Build items needed by ChipNet
    const asymmetric = new ChipCrypt.AsymmetricImpl()
    const keyPairBin = {
      privateKey: new Uint8Array(Buffer.from(this.pm.keys.privateKey.d, 'base64url')),
      publicKey: new Uint8Array(Buffer.from(this.pm.keys.publicKey.x, 'base64url')),
    }
    const asymmetricVault = new ChipCrypt.AsymmetricVaultImpl(asymmetric, keyPairBin)

    const contextSaved = (context, path) => {   //Will call here when discovery context saved
      const sessionCode = context.query.sessionCode
      let linkIdsByNonce = this.linkMapsBySession[sessionCode];  //We will build our cache of linkIds
      if (!linkIdsByNonce) {
        linkIdsByNonce = context.linkIdsByNonce;
      } else {
        linkIdsByNonce = { ...context.linkIdsByNonce, ...linkIdsByNonce };
      }
      this.linkMapsBySession[sessionCode] = linkIdsByNonce;
    }
    const participantState = new ChipNetUni.MemoryUniParticipantState(cryptoHash, contextSaved)

    const participantOptions = new ChipNetUni.UniParticipantOptions(
      (linkIntent, queryIntents) => {		// Negotiate intent
//log.debug("LQ intent CB:", linkIntent, queryIntents)
        // TODO: Reduce the min/max of lift intent to be lesser of the two
        return linkIntent
      }
    )

    const findAddress = async (query, inLinkId) => {    //ChipNet will call here to discover possible lift pathways
      const { target, intents } = query
      const { units } = intents.L
      const { key, cuid } = target.address
      const parms = [self.cuid, units, cuid, key]
      const sql = "select fori,foro,bot,out,path,inp_cuid,out_cuid,bot_uuid,top_uuid,min,max,out_chad,top_chad,out_agent from mychips.tallies_v_paths where inp_cuid = $1 and min >= $2 and (foro or (out_cuid = $3 and out_agent = $4))"
      const queryRes = await pm.db.query(sql, parms)  //Ask our local DB for possible relevant paths
      rows = queryRes?.rows
log.debug("PQ Find:", this.pm.agent, sql, parms, rows.length)   //;rows.forEach(r => { log.debug("  find:", r) })
      const selfMatchRow = rows.find(r => (!r.foro && r.out_agent == key && r.out_cuid == cuid))  //Any row that proves I am the target
      const selfIsMatch = Boolean(selfMatchRow)
      const peerRows = rows.filter(r => (r.foro && r.out_agent == key && r.out_cuid == cuid))     //Any rows showing I am directly connected to the target
      const candRows = rows.filter(r => (r.foro && (r.out_agent != key || r.out_cuid != cuid)))   //Any rows that are external we might propagate the discovery to
      chadMap = Object.fromEntries(rows.map(r => [r.top_uuid, {to: r.out_chad, from: r.top_chad}])) //Remember all chip addresses for these rows
      const peerMatch = peerRows?.map(r => ({
        match: {
          member: {
            address: { key: r.out_agent },
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
      const selfObj = {
        member: {
//          address: selfIsMatch ? { key, cuid } : { key: self.agent, cuid: self.cuid },
          address: selfIsMatch ? { key } : { key: self.agent},
          types: ['P', 'R'] //TODO: determine from DB if we are referee
        },
        //          dependsOn: TODO: can add external referees
      }

log.debug("PQ ret:", JSON.stringify(selfObj), 'sm:', selfIsMatch, 'pm:', peerMatch, 'c:', JSON.stringify(candidates))
      return { self: selfObj, selfIsMatch, peerMatch, candidates }
    }   //findAddress

    const intentSatisfied = (queryTerms, planTerms) => {  //Tell chipnet if this segment satisfies lift requirements
      return (queryTerms.units <= planTerms.min)
    }

    const queryPeer = (request, linkID) => {   //ChipNet calls here to ask us to send discovery packet to next peer
      const { to, from } = chadMap[linkID]    //We previously stored addressing info in the map
      this.addrUpdate(to)
log.debug("LQ packet send:", this.pm.agent, linkID)
      return this.requester.request(request, message => {
        const pmsg = { target: 'lift', action: 'disco', to, from, tally: linkID, request: message }
        return new Promise((resolve, reject) => this.pm.peerTransmit(pmsg, resolve, reject))
      })
    }

    const participant = new ChipNetUni.UniParticipant(
      participantOptions, participantState, asymmetricVault, cryptoHash, findAddress, intentSatisfied, queryPeer
    )
    result = {participant, participantState}
    this.discoParticipants[participantKey] = result   //Cache this participant
    return result
  }   //getDiscoParticipant

  this.local_init = async function(msg, pm) {		//Called when a new lift has been drafted locally
log.debug("Local init:", msg)
    const { target, object, seq, aux } = msg	//Grab message components
    const { pub, pay, auth } = aux
    const dmsg = {target, seq, object}		//Make minimal return message for DB
//log.debug("LI PV:", pub, auth.sign, 'c:', pay)
    isValid = await subCrypto.verify(pub, pay, auth.sign)	//Validate payor's signature
    let recipe = {context: ['draft.init']}		//;log.debug("LI isValid:", isValid)
    if (isValid) {					//;log.debug("LI AV:", pm.keys.publicKey, 'o:', object)
//log.debug("LI PK:", pm.keys.publicKey)
      const agent = noiseCrypto.sign(pm.keys.privateKey, object)	//Agent affixes its signature to the lift
      recipe.update = {status: 'init', request: 'seek', agent_auth: {agent}}
      recipe.route = true				//Check for local/external lift routes
    } else {
      recipe.update = {status: 'void'}
    }
    pm.dbProcess(dmsg, recipe, null, e=>pm.dbError(dmsg,e))   //Progress lift to next state
  }

  this.local_seek = async function(msg, pm) {		//Lift can't be executed locally, needs ChipNet
log.debug("Local seek:", msg)
    const { target, object, seq, aux } = msg	//Grab message components
    const { units } = object
    const { origin, find } = aux			//;log.debug("LS aux:", origin, 'p:', trans)
    const { cuid, agent } = find			//;log.debug("LS find:", find, 'me:', pm.agent)
    const dmsg = {target, seq, object}		//Make minimal return message for DB
//log.debug("LS o:", origin, 'p:', trans, 'u:', units)

    try {
      const { participant, participantState } = await this.getDiscoParticipant(origin)
      const originatorOptions = new ChipNetUni.UniOriginatorOptions()
      originatorOptions.debugBudget = 30000
      const address = {key: agent, cuid}    //lift terminus destination
      const originatorState = await ChipNetUni.MemoryUniOriginatorState.build(
        originatorOptions, 
        participant.state.peerLinks
      )
      const originator = new ChipNetUni.UniOriginator(originatorState, participant, participant.cryptoHash, participant.assymetricVault)
      const { plans, sessionCode } = await originator.discover(
        {address},
        {'L': {units}}
      )
      const edgeMapper = (await participantState.getContext(sessionCode, [])).linkIdsByNonce
      const mapPlans = plans.map(plan => {
        const nonce0 = plan.path[0].nonce
        const via = edgeMapper[nonce0]            //;log.debug('LS nv0', nonce0, 'v:', via)
        return { ...plan, via }
      })					//;log.debug("LS mapPlans:", JSON.stringify(mapPlans))
log.debug("LS mapPlans:", JSON.stringify(mapPlans))
      let recipe = {context: ['init.seek']}
      if (mapPlans.length) {        // Discovery succeeded
        recipe.pick = true			//Pick optimal lift route(s)
        recipe.update = {status: 'seek', request: 'exec', trans: {plans: mapPlans}}
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

  this.getTrxParticipant = async function(selfChad, getDmsg, getPmsg, sessionCode) {   //Create participant instance for lift transaction
    const participantKey = `${selfChad.agent}`		//;log.debug("Lgp pk:", participantKey)
    if (Object.hasOwn(this.trxParticipants, participantKey))    //Do we already have a participant object?
      return this.trxParticipants[participantKey]
    const nonceToLinkMap = this.linkMapsBySession[sessionCode]
    const self = {key: selfChad.agent}
    let trxParticipantState     // stateSaved will reference

    const trxResources = {
      promise: async (member, inLinks, outLinks, record) => {     //A routine to commit local chits to the lift
        const inLink = inLinks[0]     //TODO: iterate over all links
        const outLink = outLinks[0]
        const inUnits = inLink?.link?.intents?.L?.units
        const outUnits = outLink?.link?.intents?.L?.units
        let sub, context, update, promise, insert = false;
        if (inLink && outLink) {   //intermediary
          if (inUnits !== outUnits) throw Error(`Output units: ${outUnits} != input units: ${inUnits}`)
          promise = {it: inLink.linkId, ot: outLink.linkId, units: inUnits}
          context = ['null']
          update = {status: 'part'}
          insert = true
        } else if (inLink) {    //terminus
          const cuid = record?.payload?.find?.cuid ?? inLink.link?.target?.cuid   //Will the link ever have a cuid?
          sub = {agent: inLink.link?.target?.key, cuid}
          promise = {it: inLink.linkId, sub, units: inUnits}
          context = ['null']
          update = {status: 'part', payor_auth: record?.payload?.auth, find: record?.payload?.find, lift_type: 'pay'}
          insert = true
        } else if (outLink) {   //originator
          sub = {agent: outLink.link?.source?.key, cuid: selfChad.cuid}
          promise = {sub, ot: outLink.linkId, units: outUnits}
          context = ['seek.exec']
          update = {status: 'exec'}
        }
        const recipe = {promise, context, update, insert}
        const dmsg = getDmsg()
log.debug("LE pr:", this.pm.agent, 'io:', !!inLink, !!outLink, 'ol:', JSON.stringify(outLink), 'dm:', JSON.stringify(dmsg))
        const liftRec = await new Promise(    //TODO: anything we should do/check with the returned record?
          (resolve, reject) => pm.dbProcess(dmsg, recipe, resolve, e => {
              pm.dbError(dmsg, e)
              reject(e)
            }
          )
        )
      },
//      shouldCommit: async (member, inLinks, outLinks, record) => {    //Last chance to abort transaction
//        let x = this.pm.agent
//        return true;
//      },
      release: async (isSuccess, member, inLinks, outLinks, record) => {    //Routine to rollback/void chits
log.debug("LE rel:", this.pm.agent, member)
        const status = isSuccess ? 'good' : 'void'
        const recipe = {context: ['exec', 'part'], update: {status, record}}
        const links = Math.max(inLinks?.length, outLinks?.length)
        for (let i = 0; i < links; i++) {
          const dmsg = {...getDmsg(), it: inLinks?.[i]?.linkId, ot: outLinks?.[i]?.linkId}
          const result = await new Promise(
            (resolve, reject) => pm.dbProcess(dmsg, recipe, resolve, e => {
                pm.dbError(dmsg, e)
                reject(e)
              }
            )
          )
log.debug("LE result:", result)
          const newState = result?.state ?? result
          if (newState !== status) {
            log.error(`Failed to transition to status: ${status}`, this.pm.agent) //Throw error
          }
        }
      }
    }
    const stateSaved = async record => {
      const recipe = {context: ['good'], update: {record}}
      const dmsg = getDmsg()
log.debug("LE save rec:", record)
      if (await trxParticipantState.getIsReleased(record.transactionCode)) {
        const sql = "update mychips.lifts_v set record = $1 where lift_uuid = $2 and status = 'good'"
        pm.db.query(sql, [record, dmsg?.object?.lift])
        .catch(e => {
          log.error('Failed to update lift transaction record:', e?.message)
        })
      }
    }
    const tryLoadRecord = async record => {
log.debug("LE load rec:", this.pm.agent, record)
      const { seq } = getDmsg()
      if (seq !== undefined) return undefined   //I am originator, so don't bother lookup
      const uuid = record?.payload?.lift?.lift
      const { rows } = await pm.db.query('select lift_uuid, record from mychips.lifts_v where lift_uuid = $1 order by mod_date desc limit 1', [uuid])
      const row = rows[0]
      return row?.record ?? undefined
    }
    trxParticipantState = new ChipNetTrx.MemoryTrxParticipantState({
//      address: {key: self.agent, cuid: self.cuid},
      address: self,
      types: ['P', 'R']
    }, stateSaved, tryLoadRecord)

    const asymmetric = new ChipCrypt.AsymmetricImpl()
    const keyPairBin = {
      privateKey: new Uint8Array(Buffer.from(this.pm.keys.privateKey.d, 'base64url')),
      publicKey: new Uint8Array(Buffer.from(this.pm.keys.publicKey.x, 'base64url')),
    }
//    const keyPair = await asymmetric.generateKeyPairBin()
    const asymmetricVault = new ChipCrypt.AsymmetricVaultImpl(asymmetric, keyPairBin)
    const cryptoHash = new ChipCode.CryptoHashImpl()
    const updatePeer = async (address, record) => {    //ChipNet calls here for us to send update to peer
      await this.requester.request(record, async request => {
        const outLinks = Object.entries(record.topology.links).filter(([, l]) => 
          ChipNet.addressesMatch(l.source, trxParticipantState.self.address) && ChipNet.addressesMatch(l.target, address))
          .map(([nonce, link]) => nonceToLinkMap?.[nonce])
        const to = await this.addrFetch(address)
        pmsg = {...getPmsg(), to, tallies: outLinks, action: 'update', request}
log.debug("LE pT:", pmsg.from, '->', pmsg.to)
        return new Promise((resolve, reject) => this.pm.peerTransmit(pmsg, resolve, reject))
      })
log.debug("LE pX:", this.pm.agent)
    }

    const trxParticipant = new ChipNetTrx.TrxParticipant (
      trxParticipantState, asymmetricVault, asymmetric, cryptoHash, updatePeer, trxResources, nonceToLinkMap
    )
    this.trxParticipants[participantKey] = trxParticipant
    return trxParticipant
  }   //getTrxParticipant

  this.local_exec = async function(msg, pm) {		//Site requesting to advance lift to exec state
log.debug("Local exec:", msg)
    const { target, object, seq, aux } = msg	//Grab message components
    const { trans, find, origin, auth, edge } = aux			  //;log.debug("LE aux:", origin, 'p:', trans)
    const { plans, pick } = trans			        //;log.debug("LE pick:", pick)
    const plan = plans[pick]                  //Note which plan selected by the site
    this.addrUpdate(edge.out_chad)            //Remember physical address of next node
    const makeDmsg = () => ({target, seq, object})		//Build message for database
    const makePmsg = () => {		//Build message for peers
      const from = edge.inp_chad
      return {target, object, from}
    }
    const topology = {
      members: plan.members,
      links: Object.fromEntries(plan.path.map((edge, idx) => [edge.nonce, {
        source: plan.members[idx].address,
        target: plan.members[idx+1].address,
        intents: {...edge.intents, L: {units: object.units}},
      }]))
    }
    const cryptoHash = new ChipCode.CryptoHashImpl({ageMs: object.life * 1000})
    const trxRecord = {
      transactionCode: await cryptoHash.generate(),
      sessionCode: plan.sessionCode, 
      payload: {lift: object, find, auth},    //TODO: optimize what we include
      topology, 
      promises: [], 
      commits: []
    }
    const trxParticipant = await this.getTrxParticipant(origin, makeDmsg, makePmsg, plan.sessionCode);
log.debug("LE up:")
    trxParticipant.update(trxRecord)
  }	//local_exec

  this.remote_disco = async function(msg, pm) {	//Peer responding to discovery query
    const {to, from, target, tally} = msg
log.debug("Remote disco:", from.agent, from.cuid, '->', to.agent, to.cuid)

    const responder = new ChipNet.Responder(
      async (body) => {		  //Call here to build our response to a ChipNet query
        const { participant } = await this.getDiscoParticipant(to)
        const queryResult = await participant.query(body, tally);
        return queryResult;
      },
      message => {	//Call here to encapsulate and transmit our response to a query
//log.debug("L responder:", JSON.stringify(message))
        const pmsg = {to: from, from: to, target, action: 'able', request: message}
        return new Promise((resolve, reject) => this.pm.peerTransmit(pmsg, resolve, reject))
      }
    )
    
    await responder.request(msg.request)
  }	//remote_disco
  
  this.remote_able = function(msg, pm) {	//Peer discovery response
log.debug("lift remote resp:", this.pm.agent, msg.from, '->', msg.to)
    this.requester.response(msg.request)  //Just hand relevant contents to ChipNet
  }
  
  this.remote_update = async function(msg, pm) {	//Peer is sending packet regarding a lift
    const {to, from, target, object, tallies, request} = msg
    const sessionCode = request.body.sessionCode
    const getDmsg = () => ({target, object})
    const getPmsg = () => {
//      const next = {agent: address.key, cuid: address.cuid}
      return {target, object, from: to}
    }
    const cryptoHash = new ChipCode.CryptoHashImpl()
    const linkMap = Object.fromEntries(
      await Promise.all(
        tallies.map(async t => [await cryptoHash.makeNonce(t, sessionCode), t])
      )
    )
    let linkIdsByNonce = this.linkMapsBySession[sessionCode];  //We will build our cache of linkIds
    if (!linkIdsByNonce) {
      linkIdsByNonce = linkMap
    } else {
      linkIdsByNonce = { ...linkMap, ...linkIdsByNonce };
    }
    this.linkMapsBySession[sessionCode] = linkIdsByNonce;
    
log.debug("Remote update:", from.agent, '->', to.agent)

    const responder = new ChipNet.Responder(
      async (body) => {		//Call here to build response to the ChipNet query
        const participant = await this.getTrxParticipant(to, getDmsg, getPmsg, body.sessionCode)
        const fromAddress = { key: from.agent };
        await participant.update(body, fromAddress);
      },
      message => {	//Call here to encapsulate and send message to peer
//log.debug("L trx responder:", JSON.stringify(message))
        const pmsg = {to: from, from: to, target, action: 'ack', request: message}
        return new Promise((resolve, reject) => this.pm.peerTransmit(pmsg, resolve, reject))
      }
    )

    await responder.request(msg.request)
  }	//remote_update

  this.remote_ack = function(msg, pm) {	//Peer responding to lift transaction
log.debug("remote ack:", this.pm.agent, msg.from, '->', msg.to)
    this.requester.response(msg.request)  //Hand relevant contents to ChipNet
  }
}

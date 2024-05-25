//State machine map for tallies
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//- TODO:
//- 
const Crypto = require('./crypto.js')
const { Log } = require('wyclif')
var log = Log('tally')
var crypto = new Crypto(log)

module.exports = function(pm) {
  this.pm = pm
  this.test = pm.test				//Test mode, ignores signatures

  this.signCheck = function(tally, passCB, failCB) {
    let {foil, stock, sign} = tally
      , message = Object.assign({}, tally)	//;log.debug('SC2:', this.test, typeof this.test)
      , fKey = foil?.cert?.public		//;log.debug('fk:', JSON.stringify(fKey,null,2))
      , sKey = stock?.cert?.public		//;log.debug('sk:', JSON.stringify(sKey,null,2))
      , fSign = sign?.foil			;log.debug('fs:', JSON.stringify(fSign,null,2))
      , sSign = sign?.stock			;log.debug('ss:', JSON.stringify(sSign,null,2))
      , pChain = Promise.resolve()		//Default to OK
    delete message.sign				//Tally contents, minus signatures (what gets signed)
  
    if (fSign && !this.test) {				//log.debug('check fSign:', fKey)
      pChain = pChain.then(() => {
        return crypto.verify(fKey, message, fSign).then(isValid => {
          if (!isValid) {
            return Promise.reject(new Error('Invalid foil signature'))
          }
        })
      })
    }
    if (sSign && !this.test) {				//log.debug('check sSign:', sKey)
      pChain = pChain.then(() => {
        return crypto.verify(sKey, message, sSign).then(isValid => {
          if (!isValid) {
            return Promise.reject(new Error('Invalid stock signature'))
          }
        })
      })
    }

    pChain.then(() => {				//log.debug('cb(true)')
      passCB(true)
    }).catch(error => {				//log.debug('cb(false)')
      log.error('signCheck: ' + tally.uuid + '; ' + error.message)
      if (typeof failCB === 'function')
        failCB(error)
      else
        passCB(false, error)
    })
  }

  this.local_ticket = function(msg, pm) {	//Our user is asking for a draft tally via ticket, possibly over a new connection
log.debug('Local ticket:', msg)
    let {target, action, chad, token, cert} = msg
      , ticket = {token, cert}
      , pmsg = {target, action, to:chad, from:cert.chad, ticket}
//log.debug('local ticket:', pmsg, 'to:', pmsg.to, 'ticket:', pmsg.ticket)
    pm.peerTransmit(pmsg, null, e =>	//Action: transmit tally to peer
      pm.peerError(pmsg,e))
  }

  this.local_offer = function(msg, pm) {	//A draft tally has been created or modified by the user
log.debug('Local offer:', msg.from.cid, '->', msg.to.cid, msg.to.agent, msg.action)
    let pmsg = Object.assign({}, msg)
      , dmsg = {action:msg.action, target:msg.target, to: msg.from, object: {uuid:msg.object.uuid}}

    this.signCheck(msg.object, () => {		//Are any given signatures valid?
      pm.peerTransmit(pmsg, ()=>{		//Action: transmit tally to peer
        pm.dbProcess(dmsg, {			//If context = userDraft, set status = 'offer'
          context: ['draft.offer'],
          update: {status: 'offer'}, clear: true
        }, null, e=>pm.dbError(dmsg,e))
      }, e=>pm.peerError(pmsg,e))
    }, () => {
      pm.dbProcess(dmsg, {			//Set back to draft
        context: ['draft.offer'],
        update: {status: 'draft'}, clear: true
      }, null, e=>pm.dbError(dmsg,e))
    })
  }

  this.local_draft = function(msg, pm) {	//The user wants to revise the offer
log.debug('Local draft:', msg.from.cid, '->', msg.to.cid, msg.to.agent, msg.action)
    let pmsg = Object.assign({}, msg)
      , dmsg = {action:msg.action, target:msg.target, to: msg.from, object: {uuid:msg.object.uuid}}
//log.debug('Tally: userDraft:', pmsg)
    pm.peerTransmit(pmsg, ()=>{
      pm.dbProcess(dmsg, {
        context: ['offer.draft'],
        update: {status: 'draft', revision: (msg?.object?.revision ?? 1) + 1}, clear: true
      }, null, e=>pm.dbError(dmsg,e))
    }, e=>pm.peerError(pmsg,e))
  }

  this.local_void = function(msg, pm) {		//The user wants no tally with this peer
log.debug('Local void:', msg.from.cid, '->', msg.to.cid, msg.to.agent, msg.action)
    let pmsg = Object.assign({}, msg)
      , dmsg = {action:msg.action, target:msg.target, to: msg.from, object: {uuid:msg.object.uuid}}
//log.debug('Tally: userVoid:', pmsg)
    pm.peerTransmit(pmsg, ()=>{
      pm.dbProcess(dmsg, {
        context: ['offer.void'],
        update: {status: 'void'}, clear: true
      }, null, e=>pm.dbError(dmsg,e))
    }, e=>pm.peerError(pmsg,e))
  }

  this.local_open = function(msg, pm) {		//The user agrees to the peer's draft tally
log.debug('Local open:', msg.from.cid, '->', msg.to.cid, msg.to.agent, msg.action)
    let pmsg = Object.assign({}, msg)
      , dmsg = {action:msg.action, target:msg.target, to: msg.from, object: {uuid:msg.object.uuid}}

    this.signCheck(msg.object, () => {		//Are any given signatures valid?
      pm.peerTransmit(pmsg, ()=>{		//Action: transmit tally to peer
        pm.dbProcess(dmsg, {
          context: ['offer.open'],
          update: {status: 'open'}, clear: true
        }, null, e=>pm.dbError(dmsg,e))
      }, e=>pm.peerError(pmsg,e))
    }, () => {
      pm.dbProcess(dmsg, {
        context: ['offer.open'],
        update: {hold_sig: null}, clear: true, notify: true
      }, null, e=>pm.dbError(dmsg,e))
    })
  }
  
  this.remote_ticket = function(msg, pm) {	//The partner has sent us a draft tally for review
log.debug('Remote ticket:', msg, msg.ticket)
    let {token, cert} = msg.ticket
      , sql = "select mychips.token_valid($1,$2);"	//Will trigger creation/transmission of draft tally
    if (token && cert) pm.db.query(sql, [token, cert], (err, res) => {
      if (err) {pm.dbError('In token query:', err)}
    })
  }

  this.remote_offer = function(msg, pm) {	//The partner has sent us a draft tally for review
log.debug('Remote offer:', msg.from.cid, msg.from.agent, '->', msg.to.cid, msg.action)
    this.signCheck(msg.object, () => {		//Are any given signatures valid?
      pm.dbProcess(msg, {
        context: ['null','void','H.offer','P.offer'],
        upsert:	{status: 'offer'}
      }, null, e=>pm.dbError(msg,e))
    }, () => {
      pm.dbProcess(dmsg, {		//User will at least get notified
        context: ['null','void','H.offer','P.offer'],
        update: {},
        notify: true
      }, null, e=>pm.dbError(dmsg,e))
    })
  }

  this.remote_draft = function(msg, pm) {	//The partner is revising the tally
log.debug('Remote draft:', msg.from.cid, msg.from.agent, '->', msg.to.cid, msg.action)
    let dmsg = {action:msg.action, target:msg.target, to: msg.to, object: {uuid: msg.object.uuid}}
    pm.dbProcess(dmsg, {
      context: ['H.offer'],
      notify: true
    }, null, e=>pm.dbError(dmsg,e))
  }

  this.remote_void = function(msg, pm) {	//The partner wants no tally with our user
log.debug('Remote void:', msg.from.cid, msg.from.agent, '->', msg.to.cid, msg.action)
    let dmsg = {action:msg.action, target:msg.target, to: msg.to, object: {uuid: msg.object.uuid}}
    pm.dbProcess(dmsg, {
      context: ['H.offer'],
      update: {status: 'void'}
    }, null, e=>pm.dbError(dmsg,e))
  }

  this.remote_open = function(msg, pm) {	//The partner agrees to the current draft tally
log.debug('Remote open:', msg.from.cid, msg.from.agent, '->', msg.to.cid, msg.action)
    this.signCheck(msg.object, () => {		//Are any given signatures valid?
      pm.dbProcess(msg, {
        context: ['H.offer'],
        upsert: {status: 'open', chain_conf: 0}
      }, (trec) => {			//Will return with updated tally
        let sign = trec?.object?.sign	//;log.debug('  RO:', JSON.stringify(tally))
          , tally = trec?.object?.uuid
          , hash = sign?.hash
          , object = {cmd: 'ack', tally, index: 0, hash}
          , cmsg = {action:'chain', target: 'chit', to:msg.from, from: msg.to, object}
//log.debug('  ro:', JSON.stringify(cmsg))
        if (tally && hash)
          pm.peerTransmit(cmsg, null, e=>pm.peerError(pmsg,e))	//start chain consensus
      }, e=>pm.dbError(msg,e))
    }, () => {
      pm.dbProcess(dmsg, {		//User will at least get notified
        context: ['H.offer'],
        update: {},
        notify: true
      }, null, e=>pm.dbError(dmsg,e))
    })
  }
}

//State machine map for tallies
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//- TODO:
//- Fixme below: validity checks
//- 
const Crypto = require('./crypto.js')
const { Log } = require('wyclif')
var log = Log('tally')
var crypto = new Crypto(log)

const signCheck = function(tally, cb, test) {
  let {foil, stock, sign} = tally
    , message = Object.assign({}, tally)
    , fKey = foil?.cert?.public			//;log.debug('fk:', JSON.stringify(fKey,null,2))
    , sKey = stock?.cert?.public		//;log.debug('sk:', JSON.stringify(sKey,null,2))
    , fSign = sign?.foil			//;log.debug('fs:', JSON.stringify(fSign,null,2))
    , sSign = sign?.stock			//;log.debug('ss:', JSON.stringify(sSign,null,2))
    , pChain = Promise.resolve()		//Default to OK
  delete message.sign				//Tally contents, minus signatures (what gets signed)
  
  if (fSign && !test) {				//log.debug('check fSign:', fKey)
    pChain = pChain.then(() => {
      return crypto.verify(fKey, message, fSign).then(isValid => {
        if (!isValid) {
          return Promise.reject(new Error('Invalid foil signature'))
        }
      })
    })
  }
  if (sSign && !test) {				//log.debug('check sSign:', sKey)
    pChain = pChain.then(() => {
      return crypto.verify(sKey, message, sSign).then(isValid => {
        if (!isValid) {
          return Promise.reject(new Error('Invalid stock signature'))
        }
      })
    })
  }

  pChain.then(() => {				//log.debug('cb(true)')
    cb(true)
  }).catch(error => {				//log.debug('cb(false)')
    log.error('signCheck: ' + tally.uuid + '; ' + error.message)
    cb(false, error)
  })
}

module.exports = {
  signCheck,
  local: {					//Actions that can be performed in response to DB notices
    ticket: function(msg) {			//Our user is asking for a draft tally via ticket, possibly over a new connection
log.debug('Local ticket:', msg)
      let {target, action, chad, token, cert} = msg
        , ticket = {token, cert}
        , pmsg = {target, action, to:chad, from:cert.chad, ticket}
//log.debug('local ticket:', pmsg, 'to:', pmsg.to, 'ticket:', pmsg.ticket)
      this.peerTransmit(pmsg, null, e =>	//Action: transmit tally to peer
        this.peerError(pmsg,e))
    },

    offer: function(msg) {			//A draft tally has been created or modified by the user
log.debug('Local offer:', msg.from.cid, '->', msg.to.cid, msg.to.agent, msg.action)
      let pmsg = Object.assign({}, msg)
        , dmsg = {action:msg.action, target:msg.target, to: msg.from, object: {uuid:msg.object.uuid}}

      signCheck(msg.object, valid => {		//Are any given signatures valid?
        if (valid) {
          this.peerTransmit(pmsg, ()=>{		//Action: transmit tally to peer
            this.dbProcess(dmsg, {		//If context = userDraft, set status = 'offer'
              context: ['draft.offer'],
              update: {status: 'offer'}
            }, null, e=>this.dbError(dmsg,e))
          }, e=>this.peerError(pmsg,e))
        } else {
          this.dbProcess(dmsg, {			//Set back to draft
            context: ['draft.offer'],
            update: {status: 'draft'}
          }, null, e=>this.dbError(dmsg,e))
        }
      }, this.test)
    },

    draft: function(msg) {			//The user wants to revise the offer
log.debug('Local draft:', msg.from.cid, '->', msg.to.cid, msg.to.agent, msg.action)
      let pmsg = Object.assign({}, msg)
        , dmsg = {action:msg.action, target:msg.target, to: msg.from, object: {uuid:msg.object.uuid}}
//log.debug('Tally: userDraft:', pmsg)
      this.peerTransmit(pmsg, ()=>{
        this.dbProcess(dmsg, {
          context: ['offer.draft'],
          update: {status: 'draft'}
        }, null, e=>this.dbError(dmsg,e))
      }, e=>this.peerError(pmsg,e))
    },

    void: function(msg) {			//The user wants no tally with this peer
log.debug('Local void:', msg.from.cid, '->', msg.to.cid, msg.to.agent, msg.action)
      let pmsg = Object.assign({}, msg)
        , dmsg = {action:msg.action, target:msg.target, to: msg.from, object: {uuid:msg.object.uuid}}
//log.debug('Tally: userVoid:', pmsg)
      this.peerTransmit(pmsg, ()=>{
        this.dbProcess(dmsg, {
          context: ['offer.void'],
          update: {status: 'void'}
        }, null, e=>this.dbError(dmsg,e))
      }, e=>this.peerError(pmsg,e))
    },

    open: function(msg) {			//The user agrees to the peer's draft tally
log.debug('Local open:', msg.from.cid, '->', msg.to.cid, msg.to.agent, msg.action)
      let pmsg = Object.assign({}, msg)
        , dmsg = {action:msg.action, target:msg.target, to: msg.from, object: {uuid:msg.object.uuid}}
      this.peerTransmit(pmsg, ()=>{		//Action: transmit tally to peer
        this.dbProcess(dmsg, {
          context: ['offer.open'],
          update: {status: 'open'}
        }, null, e=>this.dbError(dmsg,e))
      }, e=>this.peerError(pmsg,e))
    },
  },
  
  remote: {
    ticket: function(msg) {			//The partner has sent us a draft tally for review
log.debug('Remote ticket:', msg, msg.ticket)
      let {token, cert} = msg.ticket
        , sql = "select mychips.token_valid($1,$2);"	//Will trigger creation/transmission of draft tally
      if (token && cert) this.db.query(sql, [token, cert], (err, res) => {
        if (err) {this.dbError('In token query:', err)}
      })
    },

    offer: function(msg) {		//The partner has sent us a draft tally for review
log.debug('Remote offer:', msg.from.cid, msg.from.agent, '->', msg.to.cid, msg.action)
      signCheck(msg.object, valid => {		//Are any given signatures valid?
        if (valid) {
          this.dbProcess(msg, {
            context: ['null','void','H.offer','P.offer'],
            upsert:	{status: 'offer'}
          }, null, e=>this.dbError(msg,e))
        } else {
//Fixme: What is the proper response to an invalid tally?  Currently ignoring it.
        }
      }, this.test)
    },

    draft: function(msg) {			//The partner is revising the tally
log.debug('Remote draft:', msg.from.cid, msg.from.agent, '->', msg.to.cid, msg.action)
      let dmsg = {action:msg.action, target:msg.target, to: msg.to, object: {uuid: msg.object.uuid}}
      this.dbProcess(dmsg, {
        context: ['H.offer'],
        notify: true
      }, null, e=>this.dbError(dmsg,e))
    },

    void: function(msg) {			//The partner wants no tally with our user
log.debug('Remote void:', msg.from.cid, msg.from.agent, '->', msg.to.cid, msg.action)
      let dmsg = {action:msg.action, target:msg.target, to: msg.to, object: {uuid: msg.object.uuid}}
      this.dbProcess(dmsg, {
        context: ['H.offer'],
        update: {status: 'void'}
      }, null, e=>this.dbError(dmsg,e))
    },

    open: function(msg) {			//The partner agrees to the current draft tally
log.debug('Remote open:', msg.from.cid, msg.from.agent, '->', msg.to.cid, msg.action)
      signCheck(msg.object, valid => {		//Are any given signatures valid?
        if (valid) {
          this.dbProcess(msg, {
            context: ['H.offer'],
            upsert: {status: 'open'}
          }, null, e=>this.dbError(msg,e))
        } else {
//Fixme: What is the proper response to an invalid tally?  Currently ignoring it.
        }
      }, this.test)
    }
  }
}

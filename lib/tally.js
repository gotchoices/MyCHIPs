//State machine map for tallies
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//- TODO:
//- Fixme below: validity checks
//- 
const { Log } = require('wyclif')
var log = Log('tally')

module.exports = {
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
        , dmsg = {target:msg.target, to: msg.from, object: {uuid:msg.object.uuid}}
      this.peerTransmit(pmsg, ()=>{		//Action: transmit tally to peer
        this.dbProcess(dmsg, {			//If context = userDraft, set status = 'draft'
          context: ['draft.offer'],
          update: {status: 'offer'}
        }, null, e=>this.dbError(dmsg,e))
      }, e=>this.peerError(pmsg,e))
    },

    void: function(msg) {			//The user wants no tally with this peer
log.debug('Local void:', msg.from.cid, '->', msg.to.cid, msg.to.agent, msg.action)
      let pmsg = Object.assign({}, msg)
        , dmsg = {target:msg.target, to: msg.from, object: {uuid:msg.object.uuid}}
//log.debug('Tally: userVoid:', pmsg)
      this.peerTransmit(pmsg, ()=>{
        this.dbProcess(dmsg, {
          context: ['P.offer.void'],
          update: {status: 'void'}
        }, null, e=>this.dbError(dmsg,e))
      }, e=>this.peerError(pmsg,e))
    },

    open: function(msg) {			//The user agrees to the peer's draft tally
log.debug('Local open:', msg.from.cid, '->', msg.to.cid, msg.to.agent, msg.action)
      let pmsg = Object.assign({}, msg)
        , dmsg = {target:msg.target, to: msg.from, object: {uuid:msg.object.uuid}}
      this.peerTransmit(pmsg, ()=>{		//Action: transmit tally to peer
        this.dbProcess(dmsg, {
          context: ['B.offer.open'],
          update: {status: 'open'}
        }, null, e=>this.dbError(dmsg,e))
      }, e=>this.peerError(pmsg,e))
    },

//Obsolete
//    close: function(msg) {			//The user wants to close the tally, preventing further trading except to zero the total
//log.debug('Local close:', msg.from.cid, ',', msg.to.cid, msg.to.agent, msg.action)
//      let pmsg = Object.assign({}, msg)
//        , dmsg = {target:msg.target, to: msg.from, object: {uuid:msg.object.uuid}}
//      this.peerTransmit(pmsg, ()=>{
//        this.dbProcess(dmsg, {
//          context: ['open.close'],
//          update: {status: 'close'}
//        }, null, e=>this.dbError(dmsg,e))
//      }, e=>this.peerError(pmsg,e))
//    },
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
// Fixme: Any validity checks here first?
log.debug('Remote offer:', msg.from.cid, msg.from.agent, '->', msg.to.cid, msg.action)
      this.dbProcess(msg, {
        context: ['null','void','H.offer','P.offer'],
        upsert:	{status: 'offer'}
      }, null, e=>this.dbError(msg,e))
    },

    void: function(msg) {			//The partner wants no tally with our user
log.debug('Remote void:', msg.from.cid, msg.from.agent, '->', msg.to.cid, msg.action)
      let dmsg = {target:msg.target, to: msg.to, object: {uuid: msg.object.uuid}}
      this.dbProcess(dmsg, {
        context: ['H.offer'],
        update: {status: 'void'}
      }, null, e=>this.dbError(dmsg,e))
    },

    open: function(msg) {			//The partner agrees to the current draft tally
log.debug('Remote open:', msg.from.cid, msg.from.agent, '->', msg.to.cid, msg.action)
      this.dbProcess(msg, {
        context: ['H.offer'],
        upsert: {status: 'open'}
      }, null, e=>this.dbError(msg,e))
    }

//Obsolete
//    close: function(msg) {			//The partner wants to mark this tally for closing
//log.debug('Remote close:', msg, msg.from.cid, msg.from.agent, '->', msg.to.cid, msg.action)
//      let dmsg = {target:msg.target, to: msg.to, object: {uuid: msg.object.uuid}}
//      this.dbProcess(dmsg, {
//        context: ['open'], 
//        update: {status: 'close'}
//      }, null, e=>this.dbError(dmsg,e))
//    }
  }
}

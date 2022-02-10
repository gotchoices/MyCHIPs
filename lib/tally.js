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
//log.debug('Local ticket:', msg)
      let {target, action, chad, token, cert} = msg
        , ticket = {token, cert}
        , pmsg = {target, action, to:chad, from:cert.chad, ticket}
//log.debug('local ticket:', pmsg, 'to:', pmsg.to, 'ticket:', pmsg.ticket)
      this.peerTransmit(pmsg, null, e =>	//Action: transmit tally to peer
        this.peerError(msg,e))
    },

    userDraft: function(msg) {			//A draft tally has been created or modified by the user
      let pmsg = Object.assign({}, msg, {action: 'peerProffer'})
        , dmsg = {target:msg.target, to: msg.from, object: {uuid:msg.object.uuid}}
//log.debug('Tally: userDraft:', dmsg, dmsg.to, dmsg.object)
      this.peerTransmit(pmsg, ()=>{		//Action: transmit tally to peer
        this.dbProcess(dmsg, {			//If context = userDraft, set status = 'draft'
          context: ['userDraft'],
          update: {status: 'offer'}
        }, null, e=>this.dbError(msg,e))
      }, e=>this.peerError(msg,e))
    },

    userVoid: function(msg) {			//The user wants no tally with this peer
//log.debug('tally: userVoid:', msg, msg.to, msg.to.cid, msg.to.agent)
      let pmsg = Object.assign({}, msg, {action: 'peerRefuse'})
        , dmsg = {target:msg.target, to: msg.from, object: {uuid:msg.object.uuid}}
//log.debug('Tally: userVoid:', pmsg)
      this.peerTransmit(pmsg, ()=>{
        this.dbProcess(dmsg, {
          context: ['userVoid'],
          update: {status: 'void'}
        }, null, e=>this.dbError(msg,e))
      }, e=>this.peerError(msg,e))
    },

    userAccept: function(msg) {			//The user agrees to the peer's draft tally
      let pmsg = Object.assign({}, msg, {action: 'peerAccept'})
        , dmsg = {target:msg.target, to: msg.from, object: {uuid:msg.object.uuid}}
//log.debug('tally: userAccept:', msg, msg.to, msg.to.cid, msg.to.agent)
      this.peerTransmit(pmsg, ()=>{		//Action: transmit tally to peer
        this.dbProcess(dmsg, {
          context: ['userAccept'],
          update: {status: 'open'}
        }, null, e=>this.dbError(msg,e))
      }, e=>this.peerError(msg,e))
    },

    userClose: function(msg) {			//The user wants to close the tally, preventing further trading except to zero the total
      let pmsg = Object.assign({}, msg, {action: 'peerClose'})
        , dmsg = {target:msg.target, to: msg.from, object: {uuid:msg.object.uuid}}
//log.debug('tally: userClose:', msg, msg.from, msg.to)
      this.peerTransmit(pmsg, ()=>{
        this.dbProcess(dmsg, {
          context: ['userClose'],
          update: {status: 'close'}
        }, null, e=>this.dbError(msg,e))
      }, e=>this.peerError(msg,e))
    },
  },
  
  remote: {
    ticket: function(msg) {			//The partner has sent us a draft tally for review
//log.debug('remote ticket:', msg, msg.ticket)
      let {token, cert} = msg.ticket
        , sql = "select mychips.token_valid($1,$2);"	//Will trigger creation/transmission of draft tally
      if (token && cert) this.db.query(sql, [token, cert], (err, res) => {
        if (err) {this.dbError('In token query:', err)}
      })
    },

    peerProffer: function(msg) {		//The partner has sent us a draft tally for review
      let tmpSer = JSON.stringify(msg)
// Fixme: Any validity checks here first?
//log.debug('Tally: peerProffer:', msg, msg.to)
      this.dbProcess(msg, {
        context: ['null','void','userProffer','peerProffer'],
        upsert:	true
      }, null, e=>this.dbError(msg,e))
    },

    peerRefuse: function(msg) {			//The partner wants no tally with our user
      let dmsg = {target:msg.target, to: msg.to, object: {uuid: msg.object.uuid}}
//log.debug('Tally: peerRefuse:', msg)
      this.dbProcess(dmsg, {
        context: ['userProffer'],
        update: {status: 'void'}
      }, null, e=>this.dbError(msg,e))
    },

    peerAccept: function(msg) {			//The partner agrees to the current draft tally
//log.debug('Tally: peerAccept:', msg, msg.to)
      this.dbProcess(msg, {
        context: ['userProffer'],
        upsert: true,
        update:	{status: 'open'},
      }, null, e=>this.dbError(msg,e))
    },

    peerClose: function(msg) {			//The partner wants to mark this tally for closing
      let dmsg = {target:msg.target, to: msg.to, object: {uuid: msg.object.uuid}}
//log.debug('Tally: peerClose:', msg, msg.from, msg.to)
      this.dbProcess(dmsg, {
        context: ['open'], 
        update: {status: 'close'}
      }, null, e=>this.dbError(msg,e))
    }
  }
}

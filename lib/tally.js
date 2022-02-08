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
      let {chad, token, cert} = msg
        , ticket = {token, cert}
        , pmsg = this.screen(msg, {to:chad, from:cert.chad, ticket})
//log.debug('local ticket:', pmsg, 'to:', pmsg.to, 'ticket:', pmsg.ticket)
      this.peerTransmit(pmsg, null, e =>		//Action: transmit tally to peer
        this.peerError(msg,e))
    },

    userDraft: function(msg) {			//A draft tally has been created or modified by the user
      let pmsg = Object.assign({}, msg, {action: 'peerProffer'})
        , object = {uuid: msg.object.uuid}
        , dmsg = this.screen(msg, {cid: msg.from.cid, agent: msg.from.agent, object})
//log.debug('Tally: userDraft:', pmsg, 'd:', dmsg)
      this.peerTransmit(pmsg, ()=>{		//Action: transmit tally to peer
        this.dbProcess(dmsg, {			//If context = userDraft, set status = 'draft'
          context: ['userDraft'],
          update: {status: 'offer'}
        }, null, e=>this.dbError(msg,e))
      }, e=>this.peerError(msg,e))
    },

    userVoid: function(msg) {			//The user wants no tally with this peer
      this.peerTransmit(msg, ()=>{
        this.dbProcess(msg, {
          context: ['userVoid'],
          update: {status: 'void'}
        }, null, e=>this.dbError(msg,e))
      }, e=>this.peerError(msg,e))
    },

    userAccept: function(msg) {			//The user agrees to the peer's draft tally
      let pmsg = Object.assign({}, msg, {action: 'peerAccept', user: msg.peer})
      delete pmsg['entity']; delete pmsg['peer']
      this.peerTransmit(pmsg, ()=>{		//Action: transmit tally to peer
        this.dbProcess(msg, {
          context: ['userAccept'],
          update: {status: 'open'}
        }, null, e=>this.dbError(msg,e))
      }, e=>this.peerError(msg,e))
    },

    userClose: function(msg) {			//The user wants to close the tally, preventing further trading except to zero the total
      this.peerTransmit(msg, ()=>{
        this.dbProcess(msg, {
          context: ['open'],
          update: {status: 'close'}
        }, null, e=>this.dbError(msg,e))
      }, e=>this.peerError(msg,e))
    },
  },
  
  remote: {
    ticket: function(msg) {			//The partner has sent us a draft tally for review
log.debug('remote ticket:', msg, msg.ticket)
      let {token, cert} = msg.ticket
        , sql = "select mychips.token_valid($1,$2);"	//Will trigger creation/transmission of draft tally
      if (token && cert) this.db.query(sql, [token, cert], (err, res) => {
        if (err) {this.dbError('In token query:', err)}
      })
    },

    peerProffer: function(msg) {		//The partner has sent us a draft tally for review
      let tmpSer = JSON.stringify(msg)
// Fixme: Any validity checks here first?
log.debug('Tally: peerProffer:', msg, msg.to)
      this.dbProcess(msg, {
        context: ['null','void','userProffer','peerProffer'],
        upsert:	true
      }, null, e=>this.dbError(msg,e))
    },

    peerRefuse: function(msg) {			//The partner wants no tally with our user
      this.dbProcess(msg, {
        context: ['userProffer'],
        update: {status: 'void'}
      }, null, e=>this.dbError(msg,e))
    },

    peerAccept: function(msg) {			//The partner agrees to the current draft tally
      this.dbProcess(msg, {
        context: ['userProffer'],
        upsert: true,
        update:	{status: 'open'},
//        update:	{status: 'open', part_sig: msg.user == msg.object.stock ? msg.object.signed.foil : msg.object.signed.stock}
      }, null, e=>this.dbError(msg,e))
    },

    peerClose: function(msg) {			//The partner wants to mark this tally for closing
      this.dbProcess(msg, {
        context: ['open'], 
        update: {status: 'close'}
      }, null, e=>this.dbError(msg,e))
    }
  }
}

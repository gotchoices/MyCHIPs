//State machine map for chit transactions
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//- TODO:
//- Should userValid and peerValid be consolidated to just "valid", or "open"?
//- 
// A chit describes a specified amount of CHIPs pledged from one person to 
// another and recorded on an associated tally.  A tally will typically contain
// many chits.  The tally total is the sum of its associated chits.
//
// Legitimate chit payments can arise in two different ways:
// - User A unilaterally sends a signed chit to User B
// - User B sends a draft chit, asking for User A's agreement to sign it
// In the second case, the chit will exist in a pending mode until agreed to.
//
// A positive chit implies credit flowing in the normal direction where the foil
// holder owes value to the stock holder.  A negative amount means credit 
// flowing in the opposite, or up-hill, direction:
// Stock does a positive chit:		stock+	Debit:	Request for payment
// Stock does a negative chit:		stock-	Credit:	Grant of refund (or lift)
// Foil  does a positive chit:		foil+	Credit:	Voluntary payment
// Foil  Does a negative chit:		foil-	Debit:	Request for refund (or lift)
//
// A chit can have the following states:
//   null:						no chit yet
//   userRequest:	Debit,		sig=null,	request='userRequest'
//   userInvoice:	Debit,		sig=null,	request=null
//   peerValid:		Debit,		sig=partner,	request=null
//   peerDecline:	Debit,		sig=void,	request=null
//   userDraft:		Credit,		sig=user,	request='userDraft'
//   userValid:		Credit,		sig=user,	request=null
//   peerInvoice:	Credit,		sig=null,	request=null
//   userAgree:		Credit,		sig=user,	request='userAgree'
//   userDecline:	Credit,		sig=void,	request='userDecline'
//   userVoid:		Credit,		sig=void,	request=null

const { Log } = require('wyclif')
var log = Log('chit')

module.exports = {
  local: {
    userRequest: function(msg) {		//A draft invoice has been created by the user
      let pmsg = Object.assign({}, msg, {action: 'peerInvoice', user: msg.peer})
      ;['entity','peer'].forEach((field)=>{delete pmsg[field]})
//    delete pmsg['entity']; delete pmsg['peer']
log.debug("Chit local userRequest:", msg.object.uuid, msg.object.units)
      this.peerTransmit(pmsg, ()=>{		//If I can transmit it,
        this.dbProcess(msg, {			//then mark it as sent
          context: ['userRequest'],
          update: {status: 'pend'}
        }, null, ()=>this.dbError(msg))
      }, ()=>this.peerError(msg))
    },
    userDecline: function(msg) {		//Our user has disapproved an invoice
      let pmsg = Object.assign({}, msg, {action: 'peerDecline', user: msg.peer})
      ['entity','peer'].forEach((field)=>{delete pmsg[field]})
      this.peerTransmit(pmsg, ()=>{		//If I can notify the peer
        this.dbProcess(msg, {			//then mark it as denied
          context: ['userDecline'],
          update: {status: 'void'}
        }, null, ()=>this.dbError(msg))
      }, ()=>this.peerError(msg))
    },
    userAgree: function(msg) {			//Our user has approved an invoice
      let pmsg = Object.assign({}, msg, {action: 'peerValid', user: msg.peer})
      delete pmsg['entity']; delete pmsg['peer']
      this.peerTransmit(pmsg, ()=>{		//If I can notify the peer
        this.dbProcess(msg, {			//mark it good on our end
          context: ['userAgree'], 
          update: {status: 'good'}
        }, null, ()=>this.dbError(msg))
      }, ()=>this.peerError(msg))
    },
    userDraft: function(msg) {			//Our user is sending money voluntarily
log.debug("Chit local userDraft:", msg.object)
      this.dbProcess(msg, {			//If I can commit it locally
        context: ['null', 'userDraft'], 
        update: {status: 'good'}
      }, result => {
log.debug("Chit local result:", result)
        let object; try {object = JSON.parse(result)} catch(e) {object = {}}
        let pmsg = Object.assign({}, msg, {action: 'peerValid', user: msg.peer, object})
        delete pmsg['entity']; delete pmsg['peer']
        this.peerTransmit(pmsg, ()=>{}, ()=>this.peerError(msg))	//Then attempt to notify the peer
      }, ()=>this.dbError(msg))
    }
  },

  remote: {
    peerInvoice: function(msg) {		//The partner has sent us a request for payment
      this.dbProcess(msg, {
        context: ['null', 'userVoid'], 
        upsert: {status: 'pend'}
      }, null, ()=>this.dbError(msg))
    },
    peerDecline: function(msg) {		//The partner will not make payment
      this.dbProcess(msg, {
        context: ['userInvoice'],
        update: {signature: 'declined', status: 'void'}
      }, null, ()=>this.dbError(msg))
    },
    peerTimeout: function(msg) {		//Invoice has been out too long (not implemented?)
      this.dbProcess(msg, {
        context: ['userInvoice'],
        upsert: {request: 'userRequest', status: 'void'}
      }, null, ()=>this.dbError(msg))
    },
    peerValid: function(msg) {			//The partner has sent an approved transaction
log.debug("Chit remote peerValid:", typeof msg.object, msg.object)
      this.dbProcess(msg, {
        context: ['null','userInvoice'],
        upsert: {status: 'good'}
      }, null, ()=>this.dbError(msg))
    },
  }
}

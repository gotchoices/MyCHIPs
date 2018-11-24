//State machine map for chit transactions
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
//- TODO:
//X- Figure out possible states
//X- Draw state diagram
//X- Code state action blocks
//- Use call-backs on notify and database to make actions dependent
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

var log = require('./logger')('chit')

module.exports = {			//Each key represents a possible transition action
  userRequest: function(msg) {		//A draft invoice has been created by the user
    var pmsg = Object.assign({}, msg, {action: 'peerInvoice', user: msg.peer})
    ;['entity','peer'].forEach((field)=>{delete pmsg[field]})
//    delete pmsg['entity']; delete pmsg['peer']
    this.peerTransmit(pmsg, ()=>{
      this.dbProcess(msg, {context: ['userRequest'], update: {}})
    }, ()=>{log.trace('Failure in Chit state: userRequest')})
  },
  peerDecline: function(msg) {		//The partner will not make payment
    this.dbProcess(msg, {context: ['userInvoice'], update: {signature: 'declined'}}, null, ()=>{log.trace('Failure in Chit state: peerDecline')})
  },
  peerTimeout: function(msg) {		//Invoice has been out too long
    this.dbProcess(msg, {context: ['userInvoice'], upsert: {request: 'userRequest'}}, null, ()=>{log.trace('Failure in Chit state: peerTimeout')})
  },
  peerValid: function(msg) {		//The partner agrees to the outstanding invoice
    this.dbProcess(msg, {context: ['null','userInvoice'], upsert: ''}, null, ()=>{log.trace('Failure in Chit state: peerValid')})
  },
  peerInvoice: function(msg) {		//The partner has sent us a request for payment
    this.dbProcess(msg, {context: ['null', 'userVoid'], upsert: ''}, null, ()=>{log.trace('Failure in Chit state: peerDecline')})
  },
  userDecline: function(msg) {		//Our user has disapproved an invoice
    var pmsg = Object.assign({}, msg, {action: 'peerDecline', user: msg.peer})
    ['entity','peer'].forEach((field)=>{delete pmsg[field]})
    this.peerTransmit(pmsg, ()=>{
      this.dbProcess(msg, {context: ['userDecline'], update: {}})
    }, ()=>{log.trace('Failure in Chit state: userDecline')})
  },
  userAgree: function(msg) {		//Our user has approved an invoice
    var pmsg = Object.assign({}, msg, {action: 'peerValid', user: msg.peer})
    delete pmsg['entity']; delete pmsg['peer']
    this.peerTransmit(pmsg, ()=>{
      this.dbProcess(msg, {context: ['userAgree'], update: {}})
    }, ()=>{log.trace('Failure in Chit state: userAgree')})
  },
  userDraft: function(msg) {		//The user is sending money voluntarily
    var pmsg = Object.assign({}, msg, {action: 'peerValid', user: msg.peer})
    delete pmsg['entity']; delete pmsg['peer']
    this.peerTransmit(pmsg, ()=>{
      this.dbProcess(msg, {context: ['null', 'userVoid'], update: {}})
    }, ()=>{log.trace('Failure in Chit state: userAgree')})
  }
}

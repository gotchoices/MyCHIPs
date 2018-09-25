//State machine map for tallies
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
//- TODO:
//- 
//A tally can have the following states:
//  nil:			status=void,	request=null,	(or no tally)
//  userDraft:			status=void,	request=draft,	user signature only
//  userProffer:		status=draft,	request=null,	user signature only
//  peerProffer:		status=draft,	request=null,	partner signature only
//  userVoid:			status=draft,	request=void,	partner signature only
//  accepted:			status=draft,	request=open,	both signatures
//  open:			status=open,	request=null,	both signatures
//  userClose:			status=open,	request=close,	cr/dr limits set to zero
//  closing:			status=close,	request=null,	non-zero balance
//  closed:			status=close,	request=null,	zero balance
//  undefined:			any other combination of status and request
//
// The server can respond to a variety of transition events, or actions
// Some actions are triggered by things going on in the database.  For example,
// even entering certain states may produce a notification from the DB.  In this
// case, the action will have the same name as the state that triggered it.
// In other cases, an action is triggered by a message coming from a peer.  These
// actions have their own unigue names, different than state names.
// Actions consist of a JSON message containing:
//   target: "talley",			or "chit", for example
//   action: "userRefuse",		"userAccept" etc.
//   entity: 10000,			if message comes from the DB
//   chipID: "fred_smith.chip"		if message comes from a peer
//   object: json_tally			or json_chit, if applicable
var log = require('./logger')('tally')

module.exports = {			//Each key represents a possible transition action
  userDraft: function(msg) {		//A draft tally has been created or modified by the user
    var pmsg = Object.assign({}, msg, {action: 'peerProffer', user: msg.peer})
    delete pmsg['entity']; delete pmsg['peer']
    this.peerTransmit(pmsg)		//Action: transmit tally to peer
    this.dbProcess(msg, {		//If context = userDraft, set status = 'draft'
      context:	['userDraft'],
      update:	{status: 'draft'}
    })
  },
  userRefuse: function(msg) {		//The user wants no tally with this peer
    this.peerNotify(msg)
    this.dbProcess(msg, {context: ['userVoid'],	update: {status: 'void'}})
  },
  userAccept: function(msg) {		//The user agrees to the peer's draft tally
    var pmsg = Object.assign({}, msg, {action: 'peerAccept', user: msg.peer})
    delete pmsg['entity']; delete pmsg['peer']
    this.peerTransmit(pmsg)		//Action: transmit tally to peer
    this.dbProcess(msg, {context: ['accepted'], update: {status: 'open'}})
  },
  userClose: function(msg) {		//The user wants to close the tally, preventing further trading except to zero the total
    this.peerTransmit(msg)
    this.dbProcess(msg, {context: ['open'], update: {status: 'close'}})
  },
  peerProffer: function(msg) {		//The partner has sent us a draft tally for review
// Fixme: Do any validity checks first here:
    this.dbProcess(msg, {
      context:		['null','void','userProffer','peerProffer'],
      upsert:		''
    })
    this.userNotify(msg)
  },
  peerRefuse: function(msg) {				//The partner wants no tally with our user
    this.dbProcess(msg, {context: ['userProffer'],	update: {status: 'void'}})
    this.userNotify(msg)
  },
  peerAccept: function(msg) {				//The partner agrees to the current draft tally
    this.dbProcess(msg, {
      context:	['userProffer'],	
      update:	{status: 'open', part_sig: msg.user == msg.object.stock ? msg.object.signed.foil : msg.object.signed.stock}
    })
    this.userNotify(msg)
  },
  peerClose: function(msg) {				//The partner wants to mark this tally for closing
    this.dbProcess(msg, {context: ['open'], update: {status: 'close'}})
    this.userNotify(msg)
  }
}

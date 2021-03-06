//State machine map for tallies
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//- TODO:
//X- Use call-backs on notify and database to make actions dependent
//- Fixme below: validity checks
//- Test less common states:
//-   userClose
//-   peerRefuse
//-   peerClose
//- 
//A tally can have the following states:
//  nil:		status=void,	request=null,	(or no tally)
//  userDraft:		status=void,	request=draft,	user signature only
//  userProffer:	status=draft,	request=null,	user signature only
//  peerProffer:	status=draft,	request=null,	partner signature only
//  userVoid:		status=draft,	request=void,	partner signature only
//  accepted:		status=draft,	request=open,	both signatures
//  open:		status=open,	request=null,	both signatures
//  userClose:		status=open,	request=close,	cr/dr limits set to zero
//  closing:		status=close,	request=null,	non-zero balance
//  closed:		status=close,	request=null,	zero balance
//  undefined:		any other combination of status and request
//
// The server can respond to a variety of transition events, or actions.
// Some actions are triggered by a change in the database.  For example,
// even entering a certain state may produce a notification from the DB.  In this
// case, the action will have the same name as the state that triggered it.
// In other cases, an action is triggered by a message coming from a peer.  These
// actions have their own unigue names, different than state names.
// Actions consist of a JSON message containing:
//   target: "talley",			or "chit", for example
//   action: "userRefuse",		"userAccept" etc.
//   entity: p1000,			if message comes from the DB
//   chipID: "fred_smith"		if message comes from a peer
//   object: json_tally			or json_chit, if applicable
const { Log } = require('wyclif')
var log = Log('tally')

module.exports = {
  local: {					//Actions that can be performed in response to DB notices
    userDraft: function(msg) {			//A draft tally has been created or modified by the user
      let pmsg = Object.assign({}, msg, {action: 'peerProffer', user: msg.peer})
      delete pmsg['entity']; delete pmsg['peer']
      this.peerTransmit(pmsg, ()=>{		//Action: transmit tally to peer
        this.dbProcess(msg, {			//If context = userDraft, set status = 'draft'
          context: ['userDraft'],
          update: {status: 'draft'}
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
          context: ['accepted'],
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
    peerProffer: function(msg) {			//The partner has sent us a draft tally for review
// Fixme: Any validity checks here first?
      this.dbProcess(msg, {
        context: ['null','void','userProffer','peerProffer'],
        upsert:	''
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
        update:	{status: 'open', part_sig: msg.user == msg.object.stock ? msg.object.signed.foil : msg.object.signed.stock}
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

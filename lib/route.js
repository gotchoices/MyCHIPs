//State machine map for pathway route discovery
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//- TODO:
//- 
//A partial, external pathway is represented by a record in mychips.routes.  It 
//indicates the state of an actual such pathway, or query about a hypothetical 
//such pathway, that may exist on other servers external to our own database.
//
//Use cases:
//- A user initiates a (typically conditional) request to lift to a peer 
//  somewhere on the network.  The peer might not yet be known by our database.
//- A tally is created with an upstream, outside peer known to our database, 
//  and we need to know if there are any routes through that peer that lead back 
//  to a downstream peer known to our database.
//- A downstream system has asked us if we have a way to reach a peer specified
//  by an obscured ID, and a host address.
//- An existing pathway has failed before or is stale and it is time to retry.
//- Existing pathway(s) are not supporting the size or volume of lifts our
//  users require so we want to develop more options.
//
// Unlike tallies and chits, pathway state changes don't always create 
// notifications to be transmitted to the end user.  The events that drive 
// state transitions are:
// - Triggers firing within the database
// - Polling by the server for stale records, ripe retries, etc.
// - Reactions to message received from peer servers
// 
//A route record can have the following states:
//  null:		status=void,	tries=0,	(or no request yet)
//  draft:		status=draft,
//  pending:		status=pending,			time < exp_date
//  timeout:		status=pending,	0>tries<max	time >= exp_date
//  unknown:		status=pending,	tries>=max	time >= exp_date
//  good:		status=good,			time > exp_date
//  stale:		status=good,			time >= exp_date
//  negative:		status=negative,
//
const { Log } = require('wyclif')
var log = Log('path')

//xxxxxxxxxxxxxx

module.exports = {				//Each key represents a possible transition action
  userDraft: function(msg) {			//A draft tally has been created or modified by the user
    var pmsg = Object.assign({}, msg, {action: 'peerProffer', user: msg.peer})
    delete pmsg['entity']; delete pmsg['peer']
    this.peerTransmit(pmsg, ()=>{		//Action: transmit tally to peer
      this.dbProcess(msg, {			//If context = userDraft, set status = 'draft'
        context:	['userDraft'],
        update:		{status: 'draft'}
      }, null, e=>this.dbError(msg,e))
    }, e=>this.peerError(msg,e))
  },
  userRefuse: function(msg) {			//The user wants no tally with this peer
    this.peerTransmit(msg, ()=>{
      this.dbProcess(msg, {
        context: ['userVoid'],	update: {status: 'void'}
      }, null, e=>this.dbError(msg,e))
    }, e=>this.peerError(msg,e))
  },
  userAccept: function(msg) {			//The user agrees to the peer's draft tally
    var pmsg = Object.assign({}, msg, {action: 'peerAccept', user: msg.peer})
    delete pmsg['entity']; delete pmsg['peer']
    this.peerTransmit(pmsg, ()=>{		//Action: transmit tally to peer
      this.dbProcess(msg, {
        context: ['accepted'], update: {status: 'open'}
      }, null, e=>this.dbError(msg,e))
    }, e=>this.peerError(msg,e))
  },
  userClose: function(msg) {			//The user wants to close the tally, preventing further trading except to zero the total
    this.peerTransmit(msg, ()=>{
      this.dbProcess(msg, {
        context: ['open'], update: {status: 'close'}
      }, null, e=>this.dbError(msg,e))
    }, e=>this.peerError(msg,e))
  },
  peerProffer: function(msg) {			//The partner has sent us a draft tally for review
// Fixme: Any validity checks here first?
    this.dbProcess(msg, {
      context:		['null','void','userProffer','peerProffer'],
      upsert:		''
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
      context:	['userProffer'],	
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

//State machine map for tallies
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
//- TODO:
//- 
//A tally can have the following states:
//  nil:			status=void,	request=null,	(or no tally)
//  userDraft:			status=void,	request=draft,	user signature only
//  userProffer:		status=draft,	request=null,	user signature only
//  peerProffer:		status=draft,	request=null,	peer signature only
//  userVoid:			status=draft,	request=void,	peer signature only
//  accepted:			status=draft,	request=open,	both signatures
//  open:			status=open,	request=null,	both signatures
//  userClose:			status=open,	request=close,	cr/dr limits set to zero
//  closing:			status=close,	request=null,	non-zero balance
//  closed:			status=close,	request=null,	zero balance
//  undefined:			any other combination of status and request
var log = require('./logger')('tally')

module.exports = {
  userDraft: {				//A draft tally has been created or modified by the user
    pre: function (msg) {this.peerTransmit(msg)},		//Action: transmit tally to peer
    db: {context: 'userDraft',	update: {status: 'draft'}},	//If context = userDraft, set status = 'draft'
  },
  userRefuse: {				//The user wants no tally with this peer
    pre: function(msg) {this.peerNotify(msg)},
    db: {context: 'userVoid',	update: {status: 'void'}},
  },
  userAccept: {				//The user agrees to the peer's draft tally
    pre: function(msg) {this.peerNotify(msg)},
    db: {context: 'accepted',	update: {status: 'open'}},
  },
  userClose: {				//The user wants to close the tally, preventing further trading except to zero the total
    pre: function(msg) {this.peerNotify(msg)},
    db: {context: 'open',	update: {status: 'close'}},
  },
  peerProffer: {			//The peer has sent us a draft tally for review
    pre: function(tal) {validProffer(tal)},
    db: {
      context:		['null','void','userProffer','peerProffer'],
      upsert:		'tal'
    },
    post: function(msg) {userNotify(msg)},
  },
  peerRefuse: {				//The peer wants no tally with our user
    db: {context: 'userProffer',	update: {status: 'void'}},
    post: function(msg) {userNotify(msg)},
  },
  peerAccept: {				//The peer agrees to the current draft tally
    db: {context: 'userProffer',	update: {status: 'open'}},
    post: function(msg) {userNotify(msg)},
  },
  peerClose: {				//The peer wants to mark this tally for closing
    db: {context: 'open',	update: {status: 'close'}},
    post: function(msg) {userNotify(msg)},
  }
}

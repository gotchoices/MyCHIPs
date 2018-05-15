//State machine controller
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// An agent consists of one or more state variables
// This module will track the state of one of those variables in accordance
// with a pre-defined state transition structure.
// -----------------------------------------------------------------------------
// TODO:
//X- Make simple state transition structure
//- How to process commands initiated from this end?
//- Handle dialog between user SPA and server
//- Implement chit dialogs
//- Implement lift dialogs
//- 
//- Implement state interpreter/transition machine
//- Make framework for spawning/tracking separate agents
//- 
var log = require('./logger')('states')
var fs		= require('fs')
//var Wyseman	= require('wyseman')
//var express	= require('express')

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

const tallyActions = {
  userDraft: {				//A draft tally has been created or modified by the user
    pre: (act,tal) => {peerTransmit(act,tal)},	//Action: transmit to peer
    db: {context: 'userDraft',	update: {status: 'draft'}},	//If context = userDraft, set status = 'draft'
  },
  userRefuse: {				//The user wants no tally with this peer
    pre: (act,tal) => {peerNotify(act,tal)},
    db: {context: 'userVoid',	update: {status: 'void'}},
  },
  userAccept: {				//The user agrees to the peer's draft tally
    pre: (act,tal) => {peerNotify(act,tal)},
    db: {context: 'accepted',	update: {status: 'open'}},
  },
  userClose: {				//The user wants to close the tally, preventing further trading except to zero the total
    pre: (act,tal) => {peerNotify(act,tal)},
    db: {context: 'open',	update: {status: 'close'}},
  },
  peerProffer: {			//The peer has sent us a draft tally for review
    pre: (tal) => {validProffer(tal)},
    db: {
      context:		['null','void','userProffer','peerProffer'],
      upsert:		tal
    },
    post: (act,tal) => {userNotify(act,tal)},
  },
  peerRefuse: {				//The peer wants no tally with our user
    db: {context: 'userProffer',	update: {status: 'void'}},
    post: (act,tal) => {userNotify(act,tal)},
  },
  peerAccept: {				//The peer agrees to the current draft tally
    db: {context: 'userProffer',	update: {status: 'open'}},
    post: (act,tal) => {userNotify(act,tal)},
  },
  peerClose: {				//The peer wants to mark this tally for closing
    db: {context: 'open',	update: {status: 'close'}},
    post: (act,tal) => {userNotify(act,tal)},
  }
}

module.exports = class AdminControl extends Wyseman {
  constructor(port) {
log.debug("In Admin constructor, port: " + port)
    let dbConf = {
      logger: require('../lib/logger')('admin'),
      interface: require('./interface'),
      schema: __dirname + "/schema-1.sql"
    }
    super(dbConf, port, (msg, sender) => {this.controlHandler(msg, sender)})
    
//    this.expApp = express()
//    this.expApp.listen(ExpPort)
//    this.number = 99
//    this.expApp.get('/doc', (req, res) => {
//log.debug("Got doc request")
//      res.send("Here's your doc: " + this.number)
//    })
//    setInterval(() => {this.number--}, 1000)
  }

  controlHandler(msg, sender) {
// Put any admin-specific control handlers here (which return true if action matched)
    let {id, action} = msg
log.debug("Got user request:", msg)
    if (action == "viewer") {
log.debug("  for viewer")
      return true
    } else {
      return false
    }
  }
}

//    if (tag == 'listen') tag = data;		//Just push the tag the client is listening to
//    if (lookup[tag]) {				//If we have a handler for this command
//      if (typeOf(lookup[tag])) {}
//    }

//    if (tag == 'listen' && data == 'user_list') {
//      this.db.query("select id,std_name,user_cdi,user_hid from mychips.users_v", (res) => {
//log.debug("res:" + JSON.stringify(res.rows))
//        this.sender({tag: 'user_list', data: res.rows})
//      })
//    }

//State machine map for distributed lift execution
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// See doc/Lifts for a more detailed description of the lift algorithm.
// TODO:
//X- Port from route.js
//- When might the originator cancel the lift (different from fail)
//- Cancellation shown on state diagram not implemented or tested
//- Allow peers to trim the lift amount? (Rather than just failing if route is too small)
//- How do we detect/handle a timeout (can node launch a Timeout and diddle the DB around the time the lift is expected to expire?)
//- Test/validate retries/loss of connectivity to remote sites
//- Test/validate chit consensus (multiple lifts going on at once)
//- 
//
//A lift record can have the following states:
//  null/void:		status=void,			(or no record yet)
//  init:		status=init,
//  seek:		status=seek,
//  timeout:		status=seek,			time >= exp_date
//  failed:		status=failed,
//  pend:		status=pend,
//  closed:		status=closed,
//
const { Log } = require('wyclif')
var log = Log('lift')
//const Stringify = require('json-stable-stringify')
//const Hash = require('hash.js')

module.exports = {
  local: {					//Actions invoked from local DB notices
    draft: function(msg) {			//A draft lift record has been created locally
      let public = this.pubKey
        , socket = this.pubSock
      Object.assign(msg.object, {public, socket})
log.debug("Local draft:", JSON.stringify(msg))
      this.dbProcess(msg, {			//Update DB with key,socket info
        context:	['draft'],
        update:	{request:'init', public, socket}
      }, null, e=>this.dbError(msg,e))
    },

    init: function(msg) {			//Our local draft record is now initialized
      let pmsg = Object.assign({}, msg, {action: 'query'})
log.debug("Local init:", JSON.stringify(pmsg))
//      delete pmsg.reverse; delete pmsg.back
      this.peerTransmit(pmsg, ()=>{		//Action: 
        this.dbProcess(msg, {
          context:	['init'],
          update:	{status: 'seek'}
        }, null, e=>this.dbError(msg,e))
      }, e=>this.peerError(msg,e))
    },

    relay: function(msg) {			//Our lift needs to be passed along
log.debug("Local lift relay:", JSON.stringify(msg))
      let pmsg = Object.assign({}, msg, {action: 'query'})
      this.peerTransmit(pmsg, ()=>{		//Action: 
        this.dbProcess(msg, {
          context:	['relay'],
          update:	{status: 'pend'}
        }, null, e=>this.dbError(msg,e))
      }, e=>this.peerError(msg,e))
    },

    local: function(msg) {			//Lift has been entered, destined for a local user
      let o = msg.object
        , pmsg = Object.assign({}, msg, {action: 'terminus', at: o.socket, from: msg.user, user: null})
log.debug("Local lift dest:", JSON.stringify(pmsg))
      this.peerTransmit(pmsg, ()=>{		//Action: 
        this.dbProcess(msg, {
          context:	['local'],
          update:	{status: 'pend'}
        }, null, e=>this.dbError(msg,e))
      }, e=>this.peerError(msg,e))
    },
  },

  remote: {					//Actions caused by a received peer packet
    query: function(msg, servSock) {		//A downstream peer server has asked to initiate a lift
log.debug("Remote lift query:", servSock, JSON.stringify(msg))
      this.dbProcess(msg, {
        context:	['null','void','timeout','unknown'],
        query:		''
      }, result => {
log.debug("Query result:", result, JSON.stringify(msg))
        if (result == 'fail') {
          let pmsg = Object.assign({}, msg, {at:msg.fat, here:msg.at, user:msg.from, from:msg.user, action:'fail'})		//Reverse message direction
          delete pmsg.try
log.debug("Fail return:", JSON.stringify(pmsg))
          this.peerTransmit(pmsg, null, e=>this.peerError(msg,e))
        }
      }, e=>this.dbError(msg,e))
    },

    terminus: function(msg) {			//Response from lift destination
log.debug("Remote terminus:", JSON.stringify(msg))
      this.dbProcess(msg, {
        context: ['seek', 'timeout'],
        update: {status: 'good', signature: 'Magic signature'}
      }, result => {
        let pl; try {pl = JSON.parse(result)} catch(e) {pl = {}}
        let o = msg.object
          , pmsg = Object.assign({}, msg, {action: 'commit', at: pl.return, fat:msg.at, from: msg.user, user: o.target, signature: pl.signature})
log.debug("Terminus result:", result, JSON.stringify(pmsg))
        if (pl.state == 'good') this.peerTransmit(pmsg, null, e=>this.peerError(msg,e))
      }, e=>this.dbError(msg,e))
    },

    commit: function(msg) {			//Got a commit return message from upstream
log.debug("Remote commit:", JSON.stringify(msg))
      this.dbProcess(msg, {
        context: ['pend', 'timeout'],
        update: {status: 'good', signature: msg.signature}
      }, result => {
//Fixme: better way to assure commit has made it all the way around (like make sure the sender is our immediate upstream peer?)
        if (result == 'good') return		//Our copy of the lift is already good, all finished

        let pl; try {pl = JSON.parse(result)} catch(e) {pl = {}}
        let o = msg.object
          , pmsg = Object.assign({}, msg, {action: 'commit', at: pl.return, fat:msg.at, from: msg.user, user: o.target, signature: pl.signature})
log.debug("Commit result:", result, JSON.stringify(pmsg))
        if (pl.state == 'good') this.peerTransmit(pmsg, null, e=>this.peerError(msg,e))
      }, e=>this.dbError(msg,e))
    },

    fail: function(msg) {			//The upstream partner says the lift fails somehow
log.debug("Remote fail:", JSON.stringify(msg))
      this.dbProcess(msg, {
        context: ['seek', 'timeout', 'unknown'],
        update: {status: 'failed'}
      }, null, e=>this.dbError(msg,e))
    },
  }
}

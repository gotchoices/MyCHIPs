//State machine map for chit transactions
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//- TODO:
//- 
// A positive chit implies credit flowing in the normal direction where the foil
// holder owes value to the stock holder.  A negative amount means credit 
// flowing in the opposite, or up-hill, direction:
// Stock does a positive chit:		stock+	Debit:	Request for payment
// Stock does a negative chit:		stock-	Credit:	Grant of refund (or lift)
// Foil  does a positive chit:		foil+	Credit:	Voluntary payment
// Foil  Does a negative chit:		foil-	Debit:	Request for refund (or lift)
//
const { Log } = require('wyclif')
var log = Log('chit')

module.exports = {
  local: {
    pend: function(msg) {		//A draft invoice has been created by the user
log.debug("Local pend:", JSON.stringify(msg))
      let pmsg = Object.assign({}, msg)
        , dmsg = {target:msg.target, to: msg.from, object: {tally:msg.object.tally, uuid:msg.object.uuid}}
//log.debug("Chit local pend:", dmsg, dmsg.to.cid, dmsg.uuid)
      this.peerTransmit(pmsg, ()=>{		//If I can transmit it,
        this.dbProcess(dmsg, {			//then mark it as sent
          context: ['A.draft.pend', 'A.void.pend'],
          update: {status: 'pend'}
        }, null, ()=>this.dbError(dmsg))
      }, ()=>this.peerError(pmsg))
    },

    void: function(msg) {			//Our user has rejected an invoice
log.debug("Local void:", JSON.stringify(msg))
      let pmsg = Object.assign({}, msg)
        , dmsg = {target:msg.target, to: msg.from, object: {tally:msg.object.tally, uuid:msg.object.uuid}}
      this.peerTransmit(pmsg, ()=>{		//If I can notify the peer
        this.dbProcess(dmsg, {			//then mark it as denied
          context: ['L.pend.void'],
          update: {status: 'void'}
        }, null, ()=>this.dbError(dmsg))
      }, ()=>this.peerError(pmsg))
    },

    good: function(msg) {			//Our user has approved an invoice
log.debug("Local good:", JSON.stringify(msg))
      let pmsg = Object.assign({}, msg)
        , dmsg = {target:msg.target, to: msg.from, object: {tally:msg.object.tally, uuid:msg.object.uuid}}
      this.peerTransmit(pmsg, ()=>{		//If I can notify the peer
        this.dbProcess(dmsg, {			//mark it good on our end
          context: ['L.pend.good', 'L.draft.good'],
          update: {status: 'good'}
        }, null, ()=>this.dbError(dmsg))
      }, ()=>this.peerError(pmsg))
    },

    chain: function(msg) {		//Outbound consensus packet
log.debug("Local chain:", JSON.stringify(msg))
      let pmsg = Object.assign({}, msg)
        , dmsg = {target:msg.target, to: msg.from, action:msg.action, object: {tally:msg.object.tally, uuid:msg.object.uuid}}
      this.peerTransmit(pmsg, () => {
        this.dbProcess(dmsg,			//mark packet as sent in our DB
          true, null, ()=>this.dbError(dmsg))
      }, ()=>this.peerError(pmsg))
    },
  },

  remote: {
    pend: function(msg) {			//The partner has sent us a request for payment
log.debug("Remote pend:", JSON.stringify(msg))
      this.dbProcess(msg, {
        context: ['null', 'L.void'], 
        upsert: {status: 'pend'}
      }, null, ()=>this.dbError(msg))
    },

    void: function(msg) {			//The partner will not make payment
log.debug("Remote void:", JSON.stringify(msg))
      this.dbProcess(msg, {
        context: ['A.pend'],
        update: {signature: null, status: 'void'}
      }, null, ()=>this.dbError(msg))
    },

    good: function(msg) {			//The partner has sent an approved transaction
log.debug("Remote good:", JSON.stringify(msg))
      this.dbProcess(msg, {
        context: ['null','A.pend'],
        upsert: {status: 'good'}
      }, null, ()=>this.dbError(msg))
    },

    chain: function(msg) {		//Consensus message from partner
log.debug("Remote chain:", JSON.stringify(msg))
      this.dbProcess(msg, false, null, ()=>this.dbError(msg))
    },
  }
}

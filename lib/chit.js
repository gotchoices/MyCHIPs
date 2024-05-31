//State machine map for chit transactions
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// A positive chit implies credit flowing in the normal direction where the foil
// holder owes value to the stock holder.  A negative amount means credit 
// flowing in the opposite, or up-hill, direction:
// Stock does a positive chit:		stock+	Debit:	Request for payment
// Stock does a negative chit:		stock-	Credit:	Grant of refund (or lift)
// Foil  does a positive chit:		foil+	Credit:	Voluntary payment
// Foil  Does a negative chit:		foil-	Debit:	Request for refund (or lift)
// -----------------------------------------------------------------------------
//- TODO:
//- 
const Crypto = require('./crypto.js')
const { Log } = require('wyclif')
var log = Log('chit')
var crypto = new Crypto(log)

module.exports = function(pm) {
  this.pm = pm
  this.test = pm.test
  this.db = pm.db

  this.signCheck = function(info, passCB, failCB) {
    let chit = info.object
      , { pub } = info
      , { by, date, memo, ref, tally, type, units, uuid, sign } = chit
      , message = {by, date, memo, ref, tally, type, units, uuid}	//What gets signed

    const doVerify = (pubKey, msg, signature) => {	//Validate or pass
      if (this.test)
        return Promise.resolve()
      if (!signature)
        return Promise.reject(new Error('Missing signature.'))
      return crypto.verify(pubKey, msg, signature).then(isValid => {
        if (!isValid) {
          return Promise.reject(new Error('Invalid chit signature'))
        }
      })
    }
    
    const pubCheck = (pubKey) => {		//Need a public key from the DB?
//log.debug("pubCheck:", pubKey)
      if (pubKey)
        return Promise.resolve(pubKey)		//;log.debug("Need pub:", tally, by)
      return new Promise((resolve, reject) => {
        let sql = "select part_cert->'public' as pub from mychips.tallies_v where tally_uuid = $1 and tally_type != $2"
          , parms = [tally, by]				//;log.debug('Sql:', sql, parms)
        this.db.query(sql, parms, (err, res) => {
          let row = res && res.rows ? res.rows[0] : {}	//;log.debug('row:', JSON.stringify(row))
          if (err) reject(err)
          else resolve(row.pub)
        })
      })
    }

  pubCheck(pub)
    .then(surePub => doVerify(surePub, message, sign))
    .then(() => passCB(true))
    .catch(error => {
      log.error('signCheck: ' + chit.tally + ':' + chit.uuid + '; ' + error.message)
      if (typeof failCB === 'function') {
        failCB(error)
      } else {
        passCB(false, error)
      }
    })
  }

  this.local_pend = function(msg, pm) {		//A draft invoice has been created by the user
log.debug("Local pend:", JSON.stringify(msg))
    let pmsg = Object.assign({}, msg)
      , dmsg = {target:msg.target, to: msg.from, object: {tally:msg.object.tally, uuid:msg.object.uuid}}
//log.debug("Chit local pend:", dmsg, dmsg.to.cuid, dmsg.uuid)
    pm.peerTransmit(pmsg, ()=>{			//If I can transmit it,
      pm.dbProcess(dmsg, {			//then mark it as sent
        context: ['A.draft.pend', 'A.void.pend'],
        update: {status: 'pend'}, clear: true
      }, null, ()=>pm.dbError(dmsg))
    }, ()=>pm.peerError(pmsg))
  }

  this.local_void = function(msg, pm) {		//Our user has rejected an invoice
log.debug("Local void:", JSON.stringify(msg))
    let pmsg = Object.assign({}, msg)
      , dmsg = {target:msg.target, to: msg.from, object: {tally:msg.object.tally, uuid:msg.object.uuid}}
    pm.peerTransmit(pmsg, ()=>{		//If I can notify the peer
      pm.dbProcess(dmsg, {			//then mark it as denied
        context: ['L.pend.void'],
        update: {status: 'void'}, clear: true
      }, null, ()=>pm.dbError(dmsg))
    }, ()=>pm.peerError(pmsg))
  }

  this.local_good = function(msg, pm) {		//Our user has approved an invoice
log.debug("Local good:", JSON.stringify(msg))
    let pmsg = Object.assign({}, msg)
      , dmsg = {target:msg.target, to: msg.from, object: {tally:msg.object.tally, uuid:msg.object.uuid}}
    delete pmsg.pub

    this.signCheck(msg, () => {			//Is the signature valid?
      pm.dbProcess(dmsg, {			//mark it good on our end
        context: ['L.pend.good', 'L.draft.good'],
        update: {status: 'good', chain_msg: {cmd: 'loc'}}, clear: true
      }, (chit) => {
        let {status, chain} = chit
        if (status = 'open' && chain) {		//Attempt to notify peer
          pmsg.object.chain = Object.assign({cmd: 'new'}, chain)
log.debug("LG:", JSON.stringify(pmsg))
          pm.peerTransmit(pmsg, null, ()=>pm.peerError(pmsg))
        }
      }, ()=>pm.dbError(dmsg))
    }, () => {
      pm.dbProcess(dmsg, {			//set it back to draft
        context: ['L.pend.good', 'L.draft.good'],
        update: {status: 'pend'}, clear: true
      }, null, e=>pm.dbError(dmsg,e))
    })
  }

  this.local_chain = function(msg, pm) {	//Outbound consensus packet
log.debug("Local chain:", JSON.stringify(msg))
    let pmsg = Object.assign({}, msg)
      , dmsg = {target:msg.target, to: msg.from, action:msg.action, object: {tally:msg.object.tally, uuid:msg.object.uuid}}
    pm.peerTransmit(pmsg, () => {
      pm.dbProcess(dmsg,			//mark packet as sent in our DB
        true, null, ()=>pm.dbError(dmsg))
    }, ()=>pm.peerError(pmsg))
  }

  this.remote_pend = function(msg, pm) {	//The partner has sent us a request for payment
log.debug("Remote pend:", JSON.stringify(msg))
    pm.dbProcess(msg, {
      context: ['null', 'L.void'], 
      upsert: {status: 'pend'}
    }, null, ()=>pm.dbError(msg))
  }

  this.remote_void = function(msg, pm) {	//The partner will not make payment
log.debug("Remote void:", JSON.stringify(msg))
    pm.dbProcess(msg, {
      context: ['A.pend'],
      update: {signature: null, status: 'void'}
    }, null, ()=>pm.dbError(msg))
  }

  this.remote_good = function(msg, pm) {	//The partner has sent an approved transaction
    delete msg.pub
log.debug("Remote good:", JSON.stringify(msg))
    this.signCheck(msg, () => {			//Is the signature valid?
      pm.dbProcess(msg, {
        context: ['null','A.pend'],
        upsert: {status: 'good'}
      }, null, ()=>pm.dbError(msg))
    }, () => {					//What to do with invalid chit
      log.error("Dropping invalid remote chit:", JSON.stringify(msg))
    })
  }

  this.remote_chain = function(msg, pm) {	//Consensus message from partner
log.debug("Remote chain:", JSON.stringify(msg))
    pm.dbProcess(msg, false, null, ()=>pm.dbError(msg))
  }
}

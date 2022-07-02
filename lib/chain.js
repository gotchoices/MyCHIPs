//Message processor for chit chain messages
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//- TODO:
//- 
const { Log } = require('wyclif')
var log = Log('chain')

module.exports = {
  local: {
    ack: function(msg) {		//Our local foil is acknowledging the hash
log.debug("Local ack:", JSON.stringify(msg))
      let pmsg = Object.assign({}, msg)
//Fixme: anything I should do upon successful connect?
      this.peerTransmit(pmsg, null, ()=>this.peerError(pmsg))
    },
  },

  remote: {
    ack: function(msg) {		//Acknowledge from remote foil
log.debug("Remote ack:", JSON.stringify(msg))
      this.dbProcess(msg, {}, null, ()=>this.dbError(msg))
    },
  }
}

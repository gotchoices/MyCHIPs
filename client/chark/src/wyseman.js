//Launch a singleton wyseman message handler/cache
//Copyright WyattERP.org: See LICENSE in the root of this package
// -----------------------------------------------------------------------------
//TODO:
//- Call actual local set/get routines (not dummies)
//- 

const Message = require('wyseman/lib/client_msg')
var log = console.log	//Print debug messages from library

const LocalStore = {
  set: function(key, value) {
console.log("Local set:", key, !!value)
  },

  get: function(key) {
console.log("Local get:", key)
  }
}

var instance
module.exports = (function() {
  if (!instance) instance = new Message(LocalStore, log)
  return instance
}())

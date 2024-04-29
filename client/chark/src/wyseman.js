//Launch a singleton wyseman message handler/cache
//Copyright WyattERP.org: See LICENSE in the root of this package
// -----------------------------------------------------------------------------
//TODO:
//- Call actual local set/get routines (not dummies)
//- 

const Message = require('wyseman/lib/client_msg')
var log = console.log	//Print debug messages from library
import AsyncStorage from "@react-native-async-storage/async-storage";

const LocalStore = {
  set: async function(key, value) {
console.log("Local set:", key, !!value)
  await AsyncStorage.setItem(key, JSON.stringify(value));
  },

  get: async function(key) {
    console.log("Local get:", key)
    try {
      const data = await AsyncStorage.getItem(key);
      if(data) {
        return JSON.parse(data)
      }
    } catch(err) {
      console.log('Error getting cached local data', err.message)
    }
  }
}

var instance
module.exports = (function() {
  if (!instance) instance = new Message(LocalStore, log)
  return instance
}())

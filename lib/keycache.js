//Maintain a cache of an agent's users' public keys to avoid duplicate queries
//Copyright WyattERP.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- Basic implementation
//- How to reset cache item if a user changes his key
//- 

//Singleton instance watches keydata queries for all connections
module.exports = {
  
  init: function(db, log) {		//Initialize module
    this.db = db
    this.log = log
    this.clear()
  },
  
  clear: function() {
    this.keyCache = {}
  },
  
//  refetch: function() {				//Refetch all loaded views from DB
//log.debug('KR:', Object.keys(keyCache))
//    if (requestCB)
//      Object.keys(keyCache).forEach(v => requestCB(v))
//  },
  
  get: function(user, cb) {		//Get key data for this user
  
    return keyCache[user]		//;log.debug("KC user:", user)
  },

}

//Crypto routines for key generation/verification
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 
const Os = require('os')
const webCrypto = require('crypto').webcrypto
const Subtle = webCrypto.subtle

const KeyConfig = {
  name: 'ECDSA',
  namedCurve: 'P-521',
  hash: {name: 'SHA-384'}
}

//Singleton instance to provide functions
module.exports = {
  init: function(log) {
    this.log = log
  },

  generate: function(cb) {		this.log.debug("Generating keypair:")
    let keys, private, publib
    Subtle.generateKey(KeyConfig, true, ['sign','verify']).then(keyPair => {
      keys = keyPair
      private = keyPair.privateKey
      return Subtle.exportKey('jwk', keyPair.publicKey)
    }).then(pubKey => {
      public = pubKey
      return Subtle.exportKey('jwk', private)
    }).then(privKey => {
      private = privKey
      cb(keys, private, public)
    }).catch(err => {
      this.log.error('Crypto generate: ' + err.message)
    })
  },

  sign: function(key, message, cb) {
    let encoder = new TextEncoder()
      , keyPromise

    if (typeof key === 'string') try {		//Get key into proper format
      key = JSON.parse(key)
    } catch (err) {
      this.log.error('Invalid key: ' + err.message)
      return
    }
    
    if (typeof key === 'object' && key?.kty) {
      keyPromise = Subtle.importKey ('jwk', key, KeyConfig, true, ['sign'])
    } else {
      keyPromise = Promise.resolve(key)
    }

    keyPromise.then(keyObj => {
      return Subtle.sign(KeyConfig, keyObj, encoder.encode(message))
    }).then(sign => {				this.log.debug("  signed:", sign, typeof sign)
      cb(sign)
    }).catch(err => {
      this.log.error('Crypto sign: ' + err.message)
    })  
  },
  
  verify: function() {
  },
  
}

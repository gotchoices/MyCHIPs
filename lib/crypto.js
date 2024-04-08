//Crypto routines for key generation/verification
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 
const Os = require('os')
const webCrypto = require('crypto').webcrypto
const Subtle = webCrypto.subtle
const Stringify = require('json-stable-stringify')

const KeyConfig = {
  name: 'ECDSA',
  namedCurve: 'P-521',
  hash: {name: 'SHA-384'}
}

module.exports = class {
  constructor (log) {
    this.log = log
  }

  generate(cb) {			//this.log.debug("Generating keypair:")
    return new Promise((resolve, reject) => {
      let keys, priv, publ
      Subtle.generateKey(KeyConfig, true, ['sign','verify']).then(keyPair => {
        keys = keyPair
        priv = keyPair.privateKey
        return Subtle.exportKey('jwk', keyPair.publicKey)
      }).then(pubKey => {
        publ = pubKey
        return Subtle.exportKey('jwk', priv)
      }).then(privKey => {
        priv = privKey
        if (cb)
          cb(keys, priv, publ)
        else
          resolve({keys, priv, publ})
      }).catch(err => {
        if (cb)
          cb(null, null, null, err)
        else
          reject(err)
        this.log.error('Crypto generate: ' + err.message)
      })
    })
  }

  sign(key, message, cb) {
    let encoder = new TextEncoder()
      , keyPromise
  
    return new Promise((resolve, reject) => {
      if (typeof key === 'string') {		//this.log.debug('Sign K:', key)
        try {
          key = JSON.parse(key)
        } catch (err) {
          this.log.error('Invalid key: ' + err.message)
          reject(err)
          return
        }
      }
  
      if (typeof key === 'object' && key?.kty) {
        keyPromise = Subtle.importKey('jwk', key, KeyConfig, true, ['sign'])
      } else {
        keyPromise = Promise.resolve(key)
      }
  
      if (typeof message === 'object') {
        message = Stringify(message)
      }
  
      keyPromise.then(keyObj => {		//this.log.debug('Sign M:', message)
        return Subtle.sign(KeyConfig, keyObj, encoder.encode(message))
      }).then(signature => {
        if (cb) cb(signature)
        resolve(signature)
      }).catch(err => {
        this.log.error('Crypto sign: ' + err.message)
        if (cb) cb(null, err)
        reject(err)
      })
    })
  }
  
  verify(key, message, signature, cb) {
    let encoder = new TextEncoder()
      , keyPromise
  
    return new Promise((resolve, reject) => {
      if (typeof key === 'string') {
        try {
          key = JSON.parse(key)			//;this.log.debug("Parse key:", key)
        } catch (err) {
          this.log.error('Invalid key: ' + err.message)
          reject(err)
          return
        }
      }

      if (typeof key === 'object' && key?.kty) {
        keyPromise = Subtle.importKey('jwk', key, KeyConfig, true, ['verify'])
      } else {
        keyPromise = Promise.resolve(key)
      }
  
      if (typeof message === 'object') {
        message = Stringify(message)		//;this.log.debug("Veri M:", message)
      }
  
      if (typeof signature === 'string') {	//this.log.debug("Veri S:", signature)
        signature = Buffer.from(signature, 'base64url')
      }
  
      keyPromise.then(keyObj => {		//this.log.debug('Veri:', message)
        return Subtle.verify(KeyConfig, keyObj, signature, encoder.encode(message))
      }).then(isValid => {
        if (cb) cb(isValid)
        resolve(isValid)
      }).catch(err => {
        this.log.error('Crypto verify: ' + err.message)
        if (cb) cb(null, err)
        reject(err)
      })
    })
  }
}

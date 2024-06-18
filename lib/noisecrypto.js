//Routines for key generation, signing, verification compatible with noise protocol
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 
const Stringify = require('json-stable-stringify')
const ChipCrypt = require('chipcrypt')
const Crypto = require('crypto')
const KeyConfig = 'x25519'

module.exports = class {
  constructor (log) {
    this.log = log
  }

  generate(cb) {			//this.log.debug("Generating keypair:")
    return new Promise((resolve, reject) => {
      Crypto.generateKeyPair(KeyConfig).then(keys => {
        const priv = keys.privateKey.export({ type: 'pkcs8', format: 'jwk' });
        const publ = keys.publicKey.export({ type: 'spki', format: 'jwk' });
          
        if (cb)
          cb(keys, priv, publ)
        else
          resolve({keys, priv, publ})
      }).catch(err => {			//this.log.debug('Err CB', !!cb, err.message)
        if (cb)
          cb(undefined, undefined, undefined, err)
        else
          reject(err)
        this.log.error('Crypto generate: ' + err.message)
      })
    })
  }

  sign(key, message, cb) {
    return new Promise((resolve, reject) => {
      if (typeof key === 'string') {
        try {
          key = JSON.parse(key)
        } catch (err) {
          this.log.error('Invalid key: ' + err.message)
          reject(err)
          return
        }
      }					//this.log.debug('AC Sign K:', key)
  
      if (typeof key === 'object' && key?.kty) try {
        key = Crypto.createPrivateKey({key, format: 'jwk'})
      } catch {
        this.log.error('Invalid key:', key)
      }
  
      if (typeof message === 'object') {
        message = Stringify(message)	//;this.log.debug('AC Sign M:', message)
      }

//      let digest = ChipCrypt.generateDigest(message)	//;this.log.debug('AC Sign D:', Buffer.from(digest).toString('base64url'))
      let digest = Crypto.createHash('sha256').update(message).digest()	//;this.log.debug('AC Sign D:', Buffer.from(digest).toString('base64url'))

let signature = 'Agent Signature'
//      ChipCrypt.signDigest(key, digest).then(signature => {	//this.log.debug('AC Sign S:', signature)
        if (cb) cb(signature)
        resolve(signature)
//      }).catch(err => {
//        this.log.error('Crypto sign: ' + err.message)
//        if (cb) cb(null, err)
//        reject(err)
//      })
    })
  }
  
  verify(key, message, signature, cb) {		//Untested!
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

      if (typeof key === 'object' && key?.kty) try {
        key = Crypto.createPrivateKey({key, format: 'jwk'})
      } catch {
        this.log.error('Invalid key:', key)
      }
      
      if (typeof message === 'object') {
        message = Stringify(message)		//;this.log.debug("Veri M:", message)
      }
      let digest = ChipCrypt.generateDigest(message)
  
//      if (typeof signature === 'string') {	//this.log.debug("Veri S:", signature)
//        signature = Buffer.from(signature, 'base64url')
//      }
  
      ChipCrypt.verifyDigest(key, digest, signature).then(isValid => {
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

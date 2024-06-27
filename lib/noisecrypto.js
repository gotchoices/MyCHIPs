//Routines for key generation, signing, verification compatible with noise protocol
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 
const Stringify = require('json-stable-stringify')
const Crypto = require('crypto')
const sodium = require('sodium-native')

module.exports = class {
  constructor (log) {
    this.log = log
  }

  generate() {			//this.log.debug("Generating keypair:")
    try {
      const keys = Crypto.generateKeyPair('ed25519')
      const priv = keys.privateKey.export({ type: 'pkcs8', format: 'jwk' });
      const publ = keys.publicKey.export({ type: 'spki', format: 'jwk' });
          
      return({keys, priv, publ})
    } catch (err) {
      this.log.error('Crypto generate: ' + err.message)
      throw err
    }
  }
  
  convertEdToX(edKeys) {
    let privateKey
      , publicKey
    try {
      if (edKeys.privateKey) {
        privateKey = Buffer.alloc(sodium.crypto_scalarmult_BYTES)
        sodium.crypto_sign_ed25519_sk_to_curve25519(privateKey, edKeys.privateKey)
      }
      if (edKeys.publicKey) {
        publicKey = Buffer.alloc(sodium.crypto_scalarmult_BYTES)
        sodium.crypto_sign_ed25519_pk_to_curve25519(publicKey, edKeys.publicKey)
      }
      return({privateKey, publicKey})
    } catch (err) {
      this.log.error('Crypto convertEdToX: ' + err.message)
      throw err
    }
  }

  async sign(key, message, cb) {
    try {
      if (typeof key === 'string') {
          key = JSON.parse(key)
      }					this.log.debug('AC Sign K:', key)
  
      if (typeof key === 'object' && key?.kty) {
        key = Crypto.createPrivateKey({key, format: 'jwk'})
      }
  
      if (typeof message === 'object') {
        message = Stringify(message)	//;this.log.debug('AC Sign M:', message)
      }

this.log.debug('AC Sign Pre:', message)
      let digest = asymmetricImpl.generateDigest(message)
this.log.debug('AC Sign D:', Buffer.from(digest).toString('base64url'))

      let signature = await asymmetricImpl.signDigest(key, digest)	;this.log.debug('AC Sign S:', signature)
      return signature
    } catch (err) {
      this.log.error('NoiseCrypto sign: ' + err.message);
      throw err;
    }
  }
  
  async verify(key, message, signature) {		//Untested!
    try {
      if (typeof key === 'string') {
        key = JSON.parse(key)			//;this.log.debug("Parse key:", key)
      }

      if (typeof key === 'object' && key?.kty) {
        key = Crypto.createPrivateKey({key, format: 'jwk'})
      }
      
      if (typeof message === 'object') {
        message = Stringify(message)		//;this.log.debug("Veri M:", message)
      }
      let digest = ChipCrypt.generateDigest(message)
  
//      if (typeof signature === 'string') {	//this.log.debug("Veri S:", signature)
//        signature = Buffer.from(signature, 'base64url')
//      }
  
      let isValid = await ChipCrypt.verifyDigest(key, digest, signature)
      return(isValid)
    } catch (err) {
      this.log.error('Crypto verify: ' + err.message)
      throw err
    }
  }
}

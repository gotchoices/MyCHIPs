//Routines for key generation, signing, verification
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//- 
const Stringify = require('json-stable-stringify')
const Crypto = require('crypto')
const Algorithm = 'Ed25519'

module.exports = class {
  constructor (log) {
    this.log = log
  }

  generate(algo = Algorithm) { 			//this.log.debug("Generating keypair:")
    try {
      const keys = Crypto.generateKeyPair(algo)
      const priv = keys.privateKey.export({ type: 'pkcs8', format: 'jwk' });
      const publ = keys.publicKey.export({ type: 'spki', format: 'jwk' });
          
      return({keys, priv, publ})
    } catch (err) {
      this.log.error('Crypto generate: ' + err.message)
      throw err
    }
  }
  
  sign(key, message, cb) {
    try {
      if (typeof key === 'string') {
        key = JSON.parse(key)
      }			//;this.log.debug('AC Sign K:', key, Buffer.isBuffer(key), key instanceof Crypto.KeyObject)

      if (typeof key === 'object' && key?.kty) {	//jwk
        key = Crypto.createPrivateKey({key, format: 'jwk'})
      }
  
      if (typeof message === 'object') {
        message = Stringify(message)	//;this.log.debug('AC Sign M:', message)
      }
      const signature = Crypto.sign(null, Buffer.from(message), key).toString('base64url');
      return signature
    } catch (err) {
      this.log.error('NoiseCrypto sign: ' + err.message);
      throw err;
    }
  }
  
  verify(key, message, signature) {		//Untested!
    try {
      if (typeof key === 'string') {
        key = JSON.parse(key)			//;this.log.debug("Parse key:", key)
      }

      if (typeof key === 'object' && key?.kty) {
        key = Crypto.createPublicKey({key, format: 'jwk'})
      }
      
      if (typeof message === 'object') {
        message = Stringify(message)		//;this.log.debug("Veri M:", message)
      }
      if (typeof signature === 'string') {
        signature = Buffer.from(signature, 'base64url')		//;this.log.debug("Veri M:", message)
      }
      
      const isValid = Crypto.verify(null, Buffer.from(message), key, signature)
      return(isValid)
    } catch (err) {
      this.log.error('Crypto verify: ' + err.message)
      throw err
    }
  }
}

//WebCrypto routines for key generation, signing, verification
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

  async generate() {			//this.log.debug("Generating keypair:")
    try {
      let keys = await Subtle.generateKey(KeyConfig, true, ['sign','verify'])	//;this.log.debug('k', keys)
      let publ = await Subtle.exportKey('jwk', keys.publicKey)	//;this.log.debug('publ', publ)
      let priv = await Subtle.exportKey('jwk', keys.privateKey)	//;this.log.debug('priv', priv)
      return {keys, priv, publ}
    } catch (err) {
      this.log.error('Crypto generate: ' + err.message)
      throw err
    }
  }

  async sign(key, message) {
    try {  
      let encoder = new TextEncoder()
      if (typeof key === 'string') {
        key = JSON.parse(key)
      }					//this.log.debug('Sign K:', key)
  
      if (typeof key === 'object' && key?.kty) {
        key = await Subtle.importKey('jwk', key, KeyConfig, true, ['sign'])
      }
  
      if (typeof message === 'object') {
        message = Stringify(message)	//;this.log.debug('Sign M:', message)
      }
  
      let signature = await Subtle.sign(KeyConfig, key, encoder.encode(message))
      
      return signature
    } catch (err) {
      this.log.error('Crypto sign: ' + err.message)
      throw err
    }
  }

  async verify(key, message, signature) {
    let encoder = new TextEncoder();
  
    try {
      if (typeof key === 'string') {
        key = JSON.parse(key);		//this.log.debug("Parse key:", key)
      }
  
      if (typeof key === 'object' && key?.kty) {
        key = await Subtle.importKey('jwk', key, KeyConfig, true, ['verify']);
      }
  
      if (typeof message === 'object') {
        message = Stringify(message);		//this.log.debug("Veri M:", message)
      }
  
      if (typeof signature === 'string') { 	//this.log.debug("Veri S:", signature)
        signature = Buffer.from(signature, 'base64url');
      }
  
      const isValid = await Subtle.verify(KeyConfig, key, signature, encoder.encode(message));
  
      return isValid;
    } catch (err) {
      this.log.error('Crypto verify: ' + err.message);
      throw err
    }
  }
}

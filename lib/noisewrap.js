//Wrapper for Noise Protocol library
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// This is currently using npmjs.org/noise-protocol native javascript implementation.
// We provide this abstraction so as to more easily adapt to other libraries.
// Most notable alternative is noise-c.wasm
// -----------------------------------------------------------------------------
// TODO:
//- 
const Noise = require('noise-protocol')
const NoiseCS = require('noise-protocol/cipher-state')	//({ NoiseC })

module.exports = class NoiseWrap {
  constructor(config) {
    this.BufferAdd = (Noise.PKLEN + NoiseCS.MACLEN) * 2 + 1
    this.readBytes = null
    this.writeBytes = null
    this.encryptBytes = null
    this.decryptBytes = null
    this.log = config.log
  }
  
  initialize(handshake, initiator, localKey, remoteKey) {
    try {
      let prolog = Buffer.alloc(0)
      return  Noise.initialize(handshake, initiator, prolog, localKey, null, remoteKey)
    } catch(e) {
      this.log.error('Noise initialize error:', e.message)
    }
  }

  writeMessage(state, messageBuf, sendBuf) {
    try {
      let split = Noise.writeMessage(state, messageBuf, sendBuf)
      this.writeBytes = Noise.writeMessage.bytes
      return split
    } catch(e) {
      this.log.error('Noise writeMessage error:', e.message)
    }
  }

  readMessage(state, messageBuf, receiveBuf) {
    try {
      let split= Noise.readMessage(state, messageBuf, receiveBuf)
      this.readBytes = Noise.readMessage.bytes
      return split
    } catch(e) {
      this.log.error('Noise readMessage error:', e.message)
    }
  }

  destroy(state) {
    try {
      return Noise.destroy(state)
    } catch(e) {
      this.log.error('Noise destroy error:', e.message)
    }
  }

  decrypt(key, decryptBuf, messageBuf) {
    try {
      NoiseCS.decryptWithAd(key, decryptBuf, null, messageBuf)
      this.decryptBytes = NoiseCS.decryptWithAd.bytesWritten
    } catch(e) {
      this.log.error('Noise decrypt error:', e.message)
    }
  }

  encrypt(key, encryptBuf, messageBuf) {
    try {
      NoiseCS.encryptWithAd(key, encryptBuf, null, messageBuf)
      this.encryptBytes = NoiseCS.encryptWithAd.bytesWritten
    } catch(e) {
      this.log.error('Noise encrypt error:', e.message)
    }
  }
}

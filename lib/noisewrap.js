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
    this.raw = config.raw
  }
  
  initialize(handshake, initiator, localKey, remoteKey) {
    if (!this.raw) try {
      let prolog = Buffer.alloc(0)
      return  Noise.initialize(handshake, initiator, prolog, localKey, null, remoteKey)
    } catch(e) {
      this.log.error('Noise initialize error:', e.message)
    }
  }

  writeMessage(state, messageBuf, sendBuf) {
    if (!this.raw) try {
      let split = Noise.writeMessage(state, messageBuf, sendBuf)
      this.writeBytes = Noise.writeMessage.bytes
      return split
    } catch(e) {
      this.log.error('Noise writeMessage error:', e.message)
    } else {
      Buffer.copy(sendBuf, messageBuf)
    }
  }

  readMessage(state, messageBuf, receiveBuf) {
    if (!this.raw) try {
      let split= Noise.readMessage(state, messageBuf, receiveBuf)
      this.readBytes = Noise.readMessage.bytes
      return split
    } catch(e) {
      this.log.error('Noise readMessage error:', e.message)
    } else {
      Buffer.copy(messageBuf, receiveBuf)
    }
  }

  destroy(state) {
    if (!this.raw) try {
      return Noise.destroy(state)
    } catch(e) {
      this.log.error('Noise destroy error:', e.message)
    }
  }

  decrypt(key, decryptBuf, messageBuf) {
    if (!this.raw) try {
      NoiseCS.decryptWithAd(key, decryptBuf, null, messageBuf)
      this.decryptBytes = NoiseCS.decryptWithAd.bytesWritten
    } catch(e) {
      this.log.error('Noise decrypt error:', e.message)
    } else {
      Buffer.copy(messageBuf, decryptBuf)
    }
  }

  encrypt(key, encryptBuf, messageBuf) {
    if (!this.raw) try {
      NoiseCS.encryptWithAd(key, encryptBuf, null, messageBuf)
      this.encryptBytes = NoiseCS.encryptWithAd.bytesWritten
    } catch(e) {
      this.log.error('Noise encrypt error:', e.message)
    } else {
      Buffer.copy(encryptBuf, messageBuf)
    }
  }
}

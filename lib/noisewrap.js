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
    } else {
      return {}			//simulated state object
    }
  }

  keyCheck(state, key) {		//Return the remote peer's public key
this.log.debug("Key check:", state.rs, key)
    let keyBuf = Buffer.from(key)
    if (this.raw) return keyBuf		//In raw mode, we don't have a verified copy
    let rkeyBuf = Buffer.from(state.rs)
    if (Buffer.compare(rkeyBuf, keyBuf))	//In encrypted mode, let's compare to what the peer says his key is
      this.log.error("Public key discrepancy:", keyBuf.toString('hex'))
    return rkeyBuf
  }

  writeMessage(state, messageBuf, sendBuf) {
    if (!this.raw) try {
      let split = Noise.writeMessage(state, messageBuf, sendBuf)
      this.writeBytes = Noise.writeMessage.bytes
      return split
    } catch(e) {
      this.log.error('Noise writeMessage error:', e.message)
    } else {
      messageBuf.copy(sendBuf)
      this.writeBytes = messageBuf.length
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
      messageBuf.copy(receiveBuf)
      this.readBytes = messageBuf.length
    }
  }

  destroy(state) {
    if (!this.raw) try {
      return Noise.destroy(state)
    } catch(e) {
      this.log.error('Noise destroy error:', e.message)
    }
  }

  decrypt(split, decryptBuf, messageBuf) {
    if (!this.raw) try {
      NoiseCS.decryptWithAd(split.rx, decryptBuf, null, messageBuf)
      this.decryptBytes = NoiseCS.decryptWithAd.bytesWritten
    } catch(e) {
      this.log.error('Noise decrypt error:', e.message)
    } else {
      messageBuf.copy(decryptBuf)
      this.decryptBytes = messageBuf.length
    }
  }

  encrypt(split, encryptBuf, messageBuf) {
    if (!this.raw) try {
      NoiseCS.encryptWithAd(split.tx, encryptBuf, null, messageBuf)
      this.encryptBytes = NoiseCS.encryptWithAd.bytesWritten
    } catch(e) {
      this.log.error('Noise encrypt error:', e.message)
    } else {
      messageBuf.copy(encryptBuf)
      this.encryptBytes = messageBuf.length
    }
  }
}

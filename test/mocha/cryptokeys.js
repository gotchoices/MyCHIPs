#!/bin/node
//Not a regression test--just some experiments with crypto routines.

const Noise = require('noise-protocol')
const Crypto = require('crypto')
const Subtle = Crypto.webcrypto.subtle

var keyPair = Noise.keygen()		//Use libsodium to make a key
var pKey = keyPair.publicKey
//var sKey = keyPair.secretKey

console.log(" Pub:", pKey.toString('hex'))

let p64Key = pKey.toString('base64')
console.log("   64:", p64Key)

let p64xKey = pKey.toString('base64url')
console.log("  64x:", p64xKey)

let poKey = Buffer.from(p64xKey,'base64').toString('hex')
console.log("   po:", poKey)

//const Zlib = require('zlib')		//Is a binary key compressable? No
//var pzBuf = Zlib.deflateSync(pKey, {level: Zlib.constants.Z_BEST_COMPRESSION})
//console.log(" Pubz:", pzBuf.toString('hex'))
//console.log("  64z:", pzBuf.toString('base64'))

let ecdh = Crypto.createECDH('secp128r1')	//Use Node Crypto library
let p1Key = ecdh.generateKeys()
console.log("p1Key:", Buffer.from(p1Key).toString('hex'), p1Key.byteLength)

let p2Pair = Crypto.generateKeyPairSync('x25519')
  , p2Pub = p2Pair.publicKey
console.log("p2Pai:", p2Pair.privateKey.export({format:'jwk'}))
console.log("p2Pub:", typeof p2Pub, p2Pub)
console.log("p2Exp:", p2Pub.export({format: 'jwk'}).x)
console.log("p2Exp:", Buffer.from(p2Pub.export({format: 'jwk'}).x, 'base64').toString('hex'))
//  , p2Key = p2Kp.export({type: 'hex'})

//Subtle.generateKey({name: 'ECDH', namedCurve:'P-256'}, true, [])
//  .then(p3Key => {
//    console.log(" p3Key :", p3Key)
//  })

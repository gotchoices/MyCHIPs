const { Schema, DB2Name, dbConf } = require('./common')
const port0=65434
const port1=65435
const port2=65436
const user0 = 'p1000'
const user1 = 'p1001'
const user2 = 'p1002'
const user3 = 'p1003'
const cid0 = 'adam_smith'
const cid1 = 'james_madison'
const cid2 = 'fran_lee'
const aKey0 = 'P' + port0
const aKey1 = 'Q' + port1
const aKey2 = 'R' + port2
var host = 'localhost'
var agent0 = Buffer.from('P'+port0).toString('base64url')
var agent1 = Buffer.from('Q'+port1).toString('base64url')
var agent2 = Buffer.from(aKey2).toString('base64url')
var uKey0 = Buffer.from('X'+user0).toString('base64url')
var uKey1 = Buffer.from('Y'+user1).toString('base64url')
var uKey2 = Buffer.from('Z'+user2).toString('base64url')
var aCon0 = {host, port: port0, keys:{publicKey:aKey0}}
var aCon1 = {host, port: port1, keys:{publicKey:aKey1}}
var aCon2 = {host, port: port2, keys:{publicKey:aKey2}}

module.exports = {
  host, 
  cid0, cid1, cid2,
  user0, user1, user2, user3,
  uKey0, uKey1, uKey2,
  port0, port1, port2,
  agent0, agent1, agent2,
  aCon0, aCon1, aCon2,
  db2Conf: (log, listen, db) => {return new dbConf(log, listen, DB2Name, Schema)}
}

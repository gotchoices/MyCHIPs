const { Schema, DB2Name, dbConf, fixedKeyPair } = require('./common')
const port0=65434
const port1=65435
const port2=65436
const user0 = 'p1000'
const user1 = 'p1001'
const user2 = 'p1002'
const user3 = 'p1003'
const cuid0 = 'adam_smith'
const cuid1 = 'james_madison'
const cuid2 = 'fran_lee'
var host = 'localhost'
const aKeys0 = fixedKeyPair('A' + port0)
const aKeys1 = fixedKeyPair('A' + port1)
const aKeys2 = fixedKeyPair('A' + port2)
var agent0 = aKeys0.publicKey.x
var agent1 = aKeys1.publicKey.x
var agent2 = aKeys2.publicKey.x
var aCon0 = {host, port: port0, keys:aKeys0}
var aCon1 = {host, port: port1, keys:aKeys1}
var aCon2 = {host, port: port2, keys:aKeys2}

module.exports = {
  host, 
  cuid0, cuid1, cuid2,
  user0, user1, user2, user3,
  port0, port1, port2,
  agent0, agent1, agent2,
  aCon0, aCon1, aCon2,
  db2Conf: (log, listen, db) => {return new dbConf(log, listen, DB2Name, Schema)}
}

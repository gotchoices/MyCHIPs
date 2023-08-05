//Test database schema crypto functions
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- Add test for mychips.j2h()
//- Add test for mychips.validate()
//- Can/should we use pgcrypto as opposed to python crypto?
//- 
const Fs = require('fs')
const Bs58 = require('bs58')
const assert = require("assert");
const { DBName, DBAdmin, testLog, Schema, dbClient } = require('./common')
const WordFile = '/usr/share/dict/words'
const Words = 6
const Cycles = 10
var log = testLog(__filename)
const dbConfig = {database:DBName, user:DBAdmin, connect:true, log, schema:Schema}

var encode_decode = function({encoder, decoder, checker}) {
  var db
  
  before('Connect to (or create) test database', function(done) {
    this.timeout(10000)		//May take a while to build database
    db = new dbClient(dbConfig, (chan, data) => {}, done)
  })

  let wordList = Fs.existsSync(WordFile) ?
      Fs.readFileSync(WordFile).toString().split("\n") :
      "Now is the time for all good men to come to the aid of their country".split(' ')
    
  for (let i = 0; i < Cycles; i++) {		//Make this many random phrases
    let wordArr = []
      , words = Math.floor(Math.random() * (Words -1)) + 1
    for (let j = 0; j < words; j++) {		//Consisting of this many random words
      let idx = Math.floor(Math.random() * wordList.length -1)
      wordArr.push(wordList[idx])
    }
    let string = wordArr.join(' ')		//Join the words together
      , strBuf = Buffer.from(string)		//;log.debug('String:', string, strBuf)
    
    it(`Encode/decode: ${string}`, function(done) {
      db.query(`select ${encoder}($1::bytea) as enc;`, [string] ,(e, res) => {if (e) done(e)
        assert.equal(res.rowCount, 1)
        let row = res.rows[0]				//Should just be one row
          , encoded = checker(string)
log.debug('Encoded:', row.enc, encoded)
        assert.equal(row.enc, encoded)
          
        db.query(`select encode(${decoder}($1),'escape') as str;`, [encoded] ,(e, res) => {if (e) done(e)
          assert.equal(res.rowCount, 1)
          let row = res.rows[0]				//Should just be one row
            , decoded = row.str.toString()
log.debug('Decoded:', decoded, string)
          assert.equal(decoded, string)
          done()
        })
      })
    })
  }
    
/* */
  after('Disconnect from test database', function() {
    db.disconnect()
  })
    
}
  

describe("Test crypto schema encoder functions", function() {

  describe('Base 64 URL-safe routines', function() {
    encode_decode({
      encoder: 'mychips.ba2b64v',
      decoder: 'mychips.b64v2ba',
      checker: str => {
        return Buffer.from(str).toString('base64url')
      }
    })
  })
  
  describe('Base 58 routines', function() {
    encode_decode({
      encoder: 'mychips.ba2b58',
      decoder: 'mychips.b582ba',
      checker: str => {
        return Bs58.encode(Buffer.from(str)).toString()
      }
    })
  })
  
});

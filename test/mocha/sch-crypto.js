//Test database schema crypto functions
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- Add test for mychips.j2h()
//- Add test for mychips.validate()
//- Can/should we use pgcrypto as opposed to python crypto?
//- 
const Fs = require('fs')
const Child = require('child_process')
const assert = require("assert");
const { Database, DBAdmin, Log, Schema } = require('../settings')
const WordFile = '/usr/share/dict/words'
const Words = 6
const Cycles = 10
var log = Log('testSchCrypto')
var { dbClient } = require("wyseman")
const dbConfig = {database:Database, user:DBAdmin, connect:true, log, schema:Schema}

describe("Test cryptographic schema functions", function() {
  var db
  this.timeout(5000)		//May take a while to build database

//  before('Delete test database', function(done) {
//    Child.exec(`dropdb --if-exists -U ${DBAdmin} ${Database}`, done)
//  })

  before('Connect to (or create) test database', function(done) {
    db = new dbClient(dbConfig, (chan, data) => {}, done)
  })

  describe('Base 64 URL-safe routines', function() {
    let wordList = Fs.readFileSync(WordFile).toString().split("\n")
    
    for (let i = 0; i < Cycles; i++) {		//Make this many random phrases
      let wordArr = []
        , words = Math.floor(Math.random() * (Words -1)) + 1
      for (let j = 0; j < words; j++) {		//Consisting of this many random words
        let idx = Math.floor(Math.random() * wordList.length -1)
        wordArr.push(wordList[idx])
      }
      let string = wordArr.join(' ')		//Join the words together
log.debug('String:', string)
    
      it(`Encode/decode: ${string}`, function(done) {
        db.query('select mychips.ba2b64v($1::bytea) as b64;', [string] ,(e, res) => {if (e) done(e)
          assert.equal(res.rowCount, 1)
          let row = res.rows[0]				//Should just be one row
            , encoded = Buffer.from(string).toString('base64url')
log.debug('Base64:', row.b64, encoded)
          assert.equal(row.b64, encoded)
          
          db.query('select mychips.b64v2ba($1) as str;', [encoded] ,(e, res) => {if (e) done(e)
            assert.equal(res.rowCount, 1)
            let row = res.rows[0]				//Should just be one row
              , decoded = row.str.toString()
log.debug('Decoded:', decoded)
            assert.equal(decoded, string)
            done()
          })
        })
      })
    }
  })

  after('Disconnect from test database', function() {
    db.disconnect()
  })
});

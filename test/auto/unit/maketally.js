//Create a valid tally for use in tally.js
//Only run this test as needed to create file: tally.json
const { testLog, libModule } = require('../common')
const Fs = require('fs')
const log = testLog(__filename)
const assert = require('assert')
const Crypto = require(libModule('crypto'))
const crypto = new Crypto(log)
const tallyFile = 'validtally.js'
var interTest = {}

tally = {
    "date": "2023-09-26T16:19:21.589681+00:00",
    "foil": {
        "cert": {
            "chad": {
                "cid": "james_madison",
                "host": "localhost",
                "port": 65435,
                "agent": "UTY1NDM1"
            },
            "date": "2023-09-26T16:19:21.583+00:00",
            "name": {
                "first": "James",
                "prefer": "Jim",
                "surname": "Madison"
            },
            "type": "p",
            "place": [
                {
                    "city": "Mytown",
                    "post": "12345-3456",
                    "type": "bill",
                    "state": "Mystate",
                    "address": "PO Box 3456",
                    "comment": "Mailing address",
                    "country": "US"
                }
            ],
            "public": {
                "x": "AJEYDQpZSvavDh6sjI6LGsxvq3CIV2Ka-B7389oQbRRo65x-hnYAO6pfIOF09e8LJpR66kuwOW9-kzS9bsHzY9VL",
                "y": "ABLDyB3qP-IIil08XteOy6MIr5sHZCKrfrio9xPZmGfWDTfFq5OxGTHKB0lWUk9D-awzJmXk-HjlDkdnw7XzusS6",
                "crv": "P-521",
                "ext": true,
                "kty": "EC",
                "key_ops": [
                    "verify"
                ]
            },
            "connect": [
                {
                    "media": "phone",
                    "address": "901-234-5678",
                    "comment": "Home"
                },
                {
                    "media": "cell",
                    "address": "901-345-6789"
                },
                {
                    "media": "email",
                    "address": "davidmadison99@gmail.com"
                }
            ],
            "identity": {
                "birth": {
                    "date": "1970-01-31",
                    "name": "Jimmy Madison",
                    "place": {
                        "city": "Mytown",
                        "post": "12345-6789",
                        "state": "Mystate",
                        "address": "1234 My Street",
                        "comment": "Birth place",
                        "country": "US"
                    }
                },
                "state": {
                    "id": "123-45-6789",
                    "country": "US"
                }
            }
        },
        "terms": {}
    },
    "sign": {
        "foil": "AHun45cKmN-jA9Ix9GIu0NWg53DFjzCK29JKn5lcdLbAKj25yGkF6zHBmuewhHh9cubTJ3BVp3x4MmoIibKzvW4PAfPmOHFn8mrBf1P5596fjA9HPiowiiKOV4fZeldxC20g5rGG5kXW31vX7GBKNNhXmdhF91-uDx6ZsL8qcIqsFFeW",
        "stock": "AQSmIZj4q05lQ8Tc4Iwh02SYJQUS2CYU4fGftd0UMoNVR82hxncSKLgwes6mc56xEnMGqYJlfhiyswEmEqvD7099AKSeVUAON7LbTXKCC_nzeUsyp9p1rLq37CkuiMRH1C8cH2RFkHuyKz7MstpafNdg5-FIJyqM2eTuVo4xztOefolZ",
    },
    "uuid": "389b7744-1ed6-503d-8786-45fd5142e920",
    "agree": {
        "name": "deluxe",
        "domain": "mychips.org",
        "version": 1
    },
    "stock": {
        "cert": {
            "chad": {
                "cid": "fran_lee",
                "host": "localhost",
                "port": 65436,
                "agent": "UjY1NDM2"
            },
            "date": "2023-09-26T16:19:21.511+00:00",
            "name": {
                "first": "Francis",
                "middle": "Scott",
                "prefer": "Fran",
                "surname": "Lee"
            },
            "type": "p",
            "place": [
                {
                    "post": "45678-1234",
                    "type": "ship",
                    "state": "Mystate",
                    "address": "4321 My Court",
                    "comment": "Summer home",
                    "country": "US"
                },
                {
                    "post": "45678-2345",
                    "type": "bill",
                    "state": "Mystate",
                    "address": "PO Box 4455",
                    "comment": "Mailing address",
                    "country": "US"
                }
            ],
            "public": {
                "x": "AVbGqQe-_W-m__5KGIYTRzqX6neQYgdu60thpc5HQBIhgneWjQXNtptyx2NnJ63E-zwPOqNBDYYwYqu_lLqIw16v",
                "y": "AcW1VUdTyoJYs6lWgTjJj3ll8KzfwOo8XgJ92uRwJdRraEFJYCMy_MVc6_o349l9jAJhh0OeOucder6ioP0uFr_f",
                "crv": "P-521",
                "ext": true,
                "kty": "EC",
                "key_ops": [
                    "verify"
                ]
            },
            "connect": [
                {
                    "media": "phone",
                    "address": "601-222-5678",
                    "comment": "Home"
                },
                {
                    "media": "cell",
                    "address": "601-222-3333"
                },
                {
                    "media": "email",
                    "address": "franlee@compuserve.com"
                }
            ],
            "identity": {
                "birth": {
                    "date": "1968-05-31"
                },
                "state": {
                    "id": "345-67-8901",
                    "country": "US"
                }
            }
        },
        "terms": {}
    },
    "comment": null,
    "version": 1
}

describe('Tally Generation', () => {

  it("set tally dates", function(done) {
    tally.date = new Date().toISOString()
    tally.stock.cert.date = new Date().toISOString()
    tally.foil.cert.date = new Date().toISOString()
    assert.ok(tally.date)
    assert.ok(tally.stock.cert.date)
    assert.ok(tally.foil.cert.date)
    done()
  })

  it("build stock key", function(done) {
    crypto.generate((keyPair, private, public) => {
      tally.stock.cert.public = public
      interTest.stockPub = public
      interTest.stockPrv = private
      assert.ok(private.x)
      assert.ok(private.y)
      done()
    })
  })

  it("build foil key", function(done) {
    crypto.generate((keyPair, private, public) => {
      tally.foil.cert.public = public
      interTest.foilPub = public
      interTest.foilPrv = private
      assert.ok(private.x)
      assert.ok(private.y)
      done()
    })
  })

  it('generate stock signature', (done) => {
    let message = Object.assign({}, tally)
    delete message.sign				;log.debug('msg:', message)
    crypto.sign(interTest.stockPrv, message, sign => {
      let textSign = Buffer.from(sign).toString('base64url')
      tally.sign.stock = textSign		;log.debug('stock sig:', sign)
      assert.ok(sign)
      done()
    })
  })
    
  it('generate foil signature', (done) => {
    let message = Object.assign({}, tally)
    delete message.sign
    crypto.sign(interTest.foilPrv, message, sign =>{
      let textSign = Buffer.from(sign).toString('base64url')
      tally.sign.foil = textSign		;log.debug('foil sig:', sign)
      done()
    })
  })
    
  it('write valid tally file', (done) => {
    tallyText = JSON.stringify(tally,null,2)		//;log.debug('tally:', tallyText)
    Fs.writeFile(tallyFile, 'module.exports = ' + tallyText + "\n", done)
  })
    
/* */
})

const assert = require('assert');

const { signCheck, local, remote } = require('../../../lib/tally');

validTally = {
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
            "file": null,
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
        "digest": null
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
            "file": null,
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

describe('Tally', () => {
    describe('SignCheck', () => {

        it('should return true when both foil and stock signatures are valid', (done) => {
            const callback = (valid, error) => {
                assert.strictEqual(error, undefined)
                assert.strictEqual(valid, true)
                done()
            }
            signCheck(validTally, callback, false);
        });

        it('should return false when foil signature is invalid', (done) => {
            let invalidFoilTally = validTally
            invalidFoilTally.foil.cert.public.x = "InvalidXValue"
            invalidFoilTally.foil.cert.public.y = "InvalidYValue"
            invalidFoilTally.sign.foil = "invalidSignValue"

            const callback = (valid, error) => {
                assert.strictEqual(error.message, 'Invalid JWK EC key')
                assert.strictEqual(valid, false)
                done()
            }
            signCheck(invalidFoilTally, callback, false);
        });

        it('should return false when stock signature is invalid', (done) => {
            let invalidStockTally = validTally
            invalidStockTally.stock.cert.public.x = "InvalidXValue"
            invalidStockTally.stock.cert.public.y = "InvalidYValue"
            invalidStockTally.sign.stock = "invalidSignValue"

            const callback = (valid, error) => {
                assert.strictEqual(error.message, 'Invalid JWK EC key')
                assert.strictEqual(valid, false)
                done()
            }
            signCheck(invalidStockTally, callback, false);
        });
    })
})
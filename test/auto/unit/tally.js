const assert = require('assert');
const Fs = require('fs');
const { testLog, libModule } = require('../common')
const log = testLog(__filename)

const Tally = require(libModule('tally'))
const tally = new Tally({})
const { signCheck } = tally
const validTally = require('./validtally.js')

describe('Tally', () => {
    
  describe('SignCheck', () => {

    it('should return true when both foil and stock signatures are valid', (done) => {
      signCheck(validTally, (valid, error) => {		//log.debug('tally:', validTally)
        assert.strictEqual(error, undefined)
        assert.strictEqual(valid, true)
        done()
      })
    })
    
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
      signCheck(invalidFoilTally, callback)
    })

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
      signCheck(invalidStockTally, callback)
    })
/* */
  })
})

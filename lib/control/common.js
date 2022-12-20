//Code common to control handlers
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//- 
const { Log } = require('wyclif')
var log = Log('control')
var qr = require('qr-image')

module.exports = {
  log,
  errCode: function(view, code, err) {
    let obj = {code: '!' + view + ':' + code}
    if (err?.code)	obj.pgCode = err.code
    if (err?.message)	obj.message = err.message
    if (err?.detail)	obj.detail = err.detail
    return obj
  }
}

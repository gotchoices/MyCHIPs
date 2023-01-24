//Code common to control handlers
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//- 
const { Log } = require('wyclif')
const { Language } = require('wyseman')
var log = Log('control')
var qr = require('qr-image')

module.exports = {
  log,
  langCode: function(view, code) {
    return '!' + view + ':' + code
  },
  errCode: function(view, code, err) {
    let obj = {code: '!' + view + ':' + code}
    if (err?.code)	obj.pgCode = err.code
    if (err?.message)	obj.message = err.message
    if (err?.detail)	obj.detail = err.detail
    return obj
  },
  buildContent: function(format, contentFunc) {
    let content
    if (typeof format == 'string')
      content = contentFunc(format)
    else if (Array.isArray(format))
      content = format.map(el => contentFunc(el))
    return content
  }
  
}

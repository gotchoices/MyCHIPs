//Action control function handlers
var log = require('./logger')('control1')
var qr = require('qr-image')

function ticket(keys, parms, cb) {
  log.debug('Calling ticket!', keys, parms)
  let image = qr.imageSync('This is a test', {type:'png'})
  cb(image)
}

function lock(keys, parms, cb) {
  log.debug('Calling lock', keys, parms)
  cb('Hello World!')
}

function unlock(keys, parms, cb) {
  log.debug('Calling unlock', keys, parms)
  cb('Hello World!')
}

function summary(keys, parms, cb) {
  log.debug('Calling summary', keys, parms)
  cb('Hello World!')
}

function trade(keys, parms, cb) {
  log.debug('Calling trade', keys, parms)
  cb('Hello World!')
//  cb(parms.values.join('-'))
}

module.exports = {
  'mychips.users_v': {
    lock	, 
    unlock	, 
    ticket:	{report: true, builder: ticket,		format: 'png',	mime:'image/png'},
    summary:	{report: true, builder: summary,	format: 'html',	mime:'application/html'},
    trade:	{report: true, builder: trade,		format: 'pdf',	mime:'application/pdf'},
  }
}

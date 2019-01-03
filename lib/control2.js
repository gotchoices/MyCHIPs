//Action control function handlers
var log = require('./logger')('control1')

function actionA(...args) {
  log.debug('Calling action A', ...args)
}

function actionB(...args) {
  log.debug('Calling action B', ...args)
}

function actionC(...args) {
  log.debug('Calling action C', ...args)
}

module.exports = {
  'mychips.covenants': {actionA, actionB, actionC}
}

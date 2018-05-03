//User client controller
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
// This module maintains a list of connected user clients.
// We will receive event packets from clients and apply necessary control logic.
// Applicable changes will be sent to the model, and then relevant updates
// will be propagated back out to any connected clients.
// -----------------------------------------------------------------------------
// TODO:
//- Accept registrations from connected clients
//- Parse incoming packets
//- Create lookup table for processing commands to handler routines
//- 
var log = require('./logger')('control')
var dataBase = require('./database')

const lookup = {
}

module.exports = class UserCont {
  constructor(ws, sender) {
    this.db = new dataBase()			//Connection to our db
    this.ws = ws
    this.sender = sender
  }

  event (msg, ws, cb) {				//Receive event from client
    log.debug("Controller got message: ", msg)
    let {tag, data} = msg
  }
}

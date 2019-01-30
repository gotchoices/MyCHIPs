//Action control function handlers
// ----------------------------------------------------------------------------
//TODO:
//- Need a way to call first time
//- The report knows whether it generates:
//-   Just wylib report content (in JSON)
//-   Just HTML content
//-   HTML content that may require more resources, like a PDF, SVG, etc.
//- Caller needs to inform builder this is the first call
//- Builder needs to inform caller if it is done, or if it needs to store state about the report
//- If the first-pass content expects callbacks, tell the caller such
//- The caller saves state, and then calls the builder again as other resources are needed
//- 
//- 
var log = require('./logger')('control1')
var qr = require('qr-image')
var wyseman = require('wyseman')

// ----------------------------------------------------------------------------
//function errMsg(msg) {
//}

// ----------------------------------------------------------------------------
function ticket(info, cb, resource) {		//Build a user authorization ticket: uses express server for included svg resource
  let {data, view, resPath, db} = info
    , {keys, options} = data
    , key = ((keys && keys[0]) ? keys[0] : {})
    , userId = parseInt(key.id)
    , error
log.debug('Calling ticket', key, options, resPath)

  if (!keys || !Array.isArray(keys) || keys.length != 1)
    error = view + '!TMK'			//Too few/many keys
  else if (!userId)
    error = view + '!IUK'			//Invalid user key

  if (!resource) {				//Build the wrapper
    let content = `<div><h4>User Ticket</h4><iframe height="400" width="400" src="${resPath}/ticket.svg"/></div>`
    cb({content, error})
    return (error == null)			//If false, not finished so cache report info

  } else if (!error && resource == 'ticket.svg') {	//Now build the actual ticket and QR code
log.debug('  building resource:', resource)
    db.query('select mychips.ticket_user($1) as ticket', [userId], (err, res)=>{
      if (err) {
        log.error("Error creating user ticket:", err.message)
      } else if (res.rows && res.rows.length == 1) {
log.debug('  got ticket:', res.rows[0], typeof res, res.rows[0])
        let json = res.rows[0].ticket
          , ticket = JSON.stringify(json)
          , svg = qr.imageSync(ticket, {type:'svg'})
        cb(null, svg)
      } else {
        cb('Invalid ticket from database')
      }
    })
  }
  return false
}

// ----------------------------------------------------------------------------
function lock(data, cb, resource) {
  let error
  log.debug('Calling lock', data)
  cb({error})
  return false
}

function unlock(data, cb, resource) {
  log.debug('Calling unlock', data)
  cb('Hello World!')
}

function summary(data, cb, resource) {
  log.debug('Calling summary', data)
  cb('<h3>Hello World!</h3>This is a test function!')
}

function trade(info, cb, resource) {
  let {data, resPath, db} = info
    , {keys, options} = data
    , key = (keys && keys.length >= 1) ? keys[0] : {}
    , error
  log.debug('Calling trade:', keys, options)
  let content = 'Hello: ' + Object.values(key).join('-') + ": " + (options ? options.start + '...' + options.end : '!')
  content += "<br>"
  for (let i = 1; i < 20; i++) {
    content += "Line " + i + '<br>'
  }
  cb({content:`<div>${content}</div>`, error})
  return false
}

module.exports = {
  'mychips.users_v': {lock, unlock, ticket, summary, trade}
}

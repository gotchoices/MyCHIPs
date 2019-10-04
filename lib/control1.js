//Action control function handlers
//Copyright MyCHIPs.org; See license in root of this package
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
const { Log } = require('wyclif')
var log = Log('control1')
var qr = require('qr-image')
var wyseman = require('wyseman')
var errCode = function(view, code) {return {code: '!' + view + '.' + code}}

// ----------------------------------------------------------------------------
//function errMsg(msg) {
//}

// ----------------------------------------------------------------------------
function ticket(info, cb, resource) {		//Build a user authorization ticket: uses express server for included svg resource
  let {data, view, resPath, db} = info
    , {keys, options} = data
    , key = ((keys && keys[0]) ? keys[0] : {})
    , userId = key.id
    , error
log.debug('Calling ticket', key, options, resPath)

  if (!keys || !Array.isArray(keys) || keys.length != 1)
    error = errCode(view, 'TMK')		//Too few/many keys
  else if (!userId)
    error = errCode(view, 'IUK')		//Invalid user key

  if (!resource) {				//Prepare report, build the wrapper
    let content = `<div>
      <h4>User Ticket</h4>
      <a href="${resPath}/ticket.json">ticket.json</a>
      <a href="${resPath}/ticket.svg">ticket.svg</a>
      <iframe height="400" width="400" src="${resPath}/ticket.svg"/>
    </div>`

log.debug('  building resources:', resource, userId)
    info.cache = {}
    db.query('select token,expires,host,port from mychips.ticket_login($1)', [userId], (err, res)=>{
      if (info.cache.error = err) {
        log.error("Error creating user ticket:", err)
        info.cache.error = err
        error = errCode(view, 'GUK')		//Generating user key
      } else if (res.rows && res.rows.length == 1) {
        info.cache.ticket = res.rows[0]
log.debug('  ticket:', info.cache.ticket)
        info.cache.json = JSON.stringify({ticket: info.cache.ticket})
      }
      cb(error, content)
    })
    return (error == null)			//If false, not finished so cache report info
  }
  if (error || info.cache.error) return false
log.debug('  resource cache:', info.cache)
  
  if (resource == 'ticket.svg') {
    let svg = qr.imageSync(info.cache.json, {type:'svg'})
    cb(null, svg)
  } else if (resource == 'ticket.json') {
    cb(null, info.cache.json)
  }
  return false
}

// ----------------------------------------------------------------------------
function lock(data, cb, resource) {
  let error
  log.debug('Calling lock', data)
  cb(error)
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

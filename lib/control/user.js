//Action control function handlers
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//- Make a general module to provide common code
//- Consolidate code in user ticket and tally invitation
//- 
const { log, errCode } = require('./common')
const Ticket = require('./ticket')
var qr = require('qr-image')

// ----------------------------------------------------------------------------
function ticket(info, cb, resource) {		//Build a user authorization ticket: uses express server for included svg resource
  if (resource) return false			//No support for http calls
  let user = process.env.MYCHIPS_REQUSER ? '' : ',token_ent as user'		//Does site require user to know their own ID?
    , sql = `select token,expires,host,port${user} from mychips.ticket_login($1)`
    , {data, view} = info
    , {options} = data

  return Ticket(info, sql, ['id'], [], (error, ticket) => {
    let content
    switch (options?.format) {
      case 'qr':
        content = qr.imageSync(JSON.stringify({ticket}), {type:'svg'})
        break
      case 'url':
        let u = user ? `&user=${ticket.user}` : ''
          , p = parseInt(ticket.port) - 1
        content = `https://${ticket.host}:${p}/user.html?&port=${ticket.port}&token=${ticket.token}${u}`
        break
      case 'link':
        content = [
          '<a href="',
          `mychips://tally?token=${ticket.token}&chad=${JSON.stringify(ticket.chad)}`,
          '">',
          '!' + view + ':TIN',
          '</a><p>',
          '!' + view + ':TIL',
          ': ', ticket.expires,
        ]
        break
      default:
        error = errCode(view, 'URF')		//Unknown report format
        break
    }
    cb(error, content)
  })
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
  cb(null, 'Hello World!')
}

function summary(data, cb, resource) {
  log.debug('Calling summary', data)
  cb(null, '<h3>Hello World!</h3>This is a test function!')
  return false
}

function trade(info, cb, resource) {
  let {data, resPath, db} = info
    , {keys, options} = data
    , key = (keys && keys.length >= 1) ? keys[0] : {}
    , error
  log.debug('Calling trade:', key, options)
  let content = 'Hello: ' + Object.values(key).join('-') + ": " + (options ? options.start + '...' + options.end : '!')
  content += "<br>"
  for (let i = 1; i < 20; i++) {
    content += "Line " + i + '<br>'
  }
  cb(error, `<div>${content}</div>`)
  return false
}

// ----------------------------------------------------------------------------
function graph(info, cb, resource) {		//Build a visual balance sheet for the user
  let {data, view, resPath, db} = info
    , {keys, options} = (data ? data : {})
    , key = ((keys && keys[0]) ? keys[0] : {})
    , error
log.debug('Calling graph:', JSON.stringify(data))

  if (!resource) {				//Prepare report, build the wrapper
log.debug('  building resources:')
    let content = ''
//      , query = 'insert into mychips.tokens_v_me (tally_seq, reuse) values ($1,$2) returning token, expires, chad'
//    info.cache = {}
//    db.query(query, [key.tally_seq, options.reuse], (err, res)=>{
//log.debug('  err:', err, ' res:', res, 'rows:', res.rows ? res.rows[0] : null)
//
//      if (info.cache.error = err) {
//        log.error("Error creating tally ticket:", err)
//        info.cache.error = err
//        error = errCode(view, 'GTT')		//Generating tally ticket
//      } else if (res.rows && res.rows.length == 1) {
//        let ticket = info.cache.ticket = res.rows[0]
////Fixme: how to encode url?
//          , url = `/tally?host=${ticket.host}&port=${ticket.port}&token=${ticket.token}`
//log.debug('  ticket:', info.cache.ticket)
//        info.cache.json = JSON.stringify({ticket})
////Fixme: get rid of english:
        content = `<div>
          <h4>Visual Balance Sheet</h4>
          <a href="${resPath}/ticket.json">ticket.json</a>
          <a href="${resPath}/ticket.svg">ticket.svg</a>
          <iframe height="400" width="400" src="${resPath}/ticket.svg"/>
        </div>`
//      }
      cb(error, content)
//    })
    return (error == null)			//If false, not finished so cache report info
  }
  if (error || info.cache.error) return false
log.debug('  resource cache:', resource, info.cache)
  
//  if (resource == 'ticket.svg') {
//    let svg = qr.imageSync(info.cache.json, {type:'svg'})
//    cb(null, svg)
//  } else if (resource == 'ticket.json') {
//    cb(null, info.cache.json)
//  }
  return false
}

module.exports = {
  'mychips.users_v': {lock, unlock, ticket, summary, trade},
  'mychips.users_v_me': {graph},
}

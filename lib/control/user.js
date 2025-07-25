//Action control function handlers
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//- Make a general module to provide common code
//- Consolidate code in user ticket and tally invitation
//- 
const { log, buildContent } = require('./common')
const Ticket = require('./ticket')
var qr = require('qr-image')

// ----------------------------------------------------------------------------
function ticket(info, cb, resource) {		//Build a user authorization ticket: uses express server for included svg resource
  if (resource) return false			//No support for http calls
  let user = process.env.MYCHIPS_REQUSER ? '' : ',token_ent as user'		//Does site require user to know their own ID?
    , sql = `select token,expires,host,port${user} from mychips.ticket_login($1)`
    , {data, view, message} = info
    , {options} = data
    , content

  return Ticket(info, sql, ['id'], [], (error, ticket) => {
    let makeContent = function(format) {
          let u = user ? `&user=${ticket.user}` : ''
            , p = parseInt(ticket.port) - 1
            , url = encodeURI(`https://${ticket.host}:${p}/user.html?&port=${ticket.port}&token=${ticket.token}${u}`)
            , link = encodeURI(`https://mychips.org/ticket?host=${ticket.host}&port=${ticket.port}&user=${ticket.user}&token=${ticket.token}`)
          switch (format) {
            case 'json':
              return {ticket}
            case 'qr':
              return qr.imageSync(link, {type:'svg'})
//              return qr.imageSync(JSON.stringify({ticket}), {type:'svg'})
            case 'url':
              let url = encodeURI(`https://${ticket.host}:${p}/user.html?&port=${ticket.port}&token=${ticket.token}${u}`)
              return '<a href="' + url +
                '">' + message('TIN').title + '</a>'
            case 'link':
              return message('TIN').help + ':\n' +
                '<a href="' + link + '">' +
                message('TIN').title +
                '</a><p>' +
                message('TIL').title +
                ': ' +
                ticket.expires
            default:
              return message('URF').title		//Unknown report format
          }
        }
    if (!error)
      content = buildContent(options?.format, makeContent)
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
    , key = keys?.[0] ?? data.key
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

module.exports = {
  'mychips.users_v': {lock, unlock, ticket, summary, trade}
}

//Action control function handlers
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//- 
const { log, errCode, langCode } = require('./common')
const Ticket = require('./ticket')
var qr = require('qr-image')

// ----------------------------------------------------------------------------
function invite(info, cb, resource) {		//Build a tally invitation: uses express server for included svg resource
  if (resource) return false			//No support for http calls
  let sql = 'insert into mychips.tokens_v_me (tally_seq, reuse) values ($1,$2) returning token, expires, chad'
    , {data, view} = info
    , {options} = data

  return Ticket(info, sql, ['tally_seq'], ['reuse'], (error, ticket) => {
    let content
    switch (options?.format) {
      case 'json':
        content = {tally: ticket}
        break
      case 'qr':
        content = qr.imageSync(JSON.stringify({ticket}), {type:'svg'})
        break
      case 'link':
        content = [
          '<a href="',
          `mychips://tally?token=${ticket.token}&chad=${JSON.stringify(ticket.chad)}`,
          '">',
          langCode(view,'TIN'),
          '</a><p>',
          langCode(view,'TIL'),
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

module.exports = {
  'mychips.tallies_v_me': {invite}
}

//Action control function handlers
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//- 
const { log, buildContent, langCode } = require('./common')
const Ticket = require('./ticket')
var qr = require('qr-image')

// ----------------------------------------------------------------------------
function invite(info, cb, resource) {		//Build a tally invitation: uses express server for included svg resource
  if (resource) return false			//No support for http calls
  let sql = 'insert into mychips.tokens_v_me (tally_seq, reuse) values ($1,$2) returning token, expires, chad'
    , {data, view, message} = info
    , {options} = data
    , content

  return Ticket(info, sql, ['tally_seq'], ['reuse'], (error, ticket) => {
    let makeContent = function(format) {
       let url = encodeURI(`https://mychips.org/tally?token=${ticket.token}&chad=${JSON.stringify(ticket.chad)}`)
          switch (format) {
            case 'json':
              return {
                ticket, url,
                title: message('TIN').title,
                message: message('TIL').title,
              }
            case 'qr':
              return qr.imageSync(JSON.stringify({ticket}), {type:'svg'})
            case 'link':
              return message('TIN').help + ':\n' +
                '<a href="' + url + '">' +
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

module.exports = {
  'mychips.tallies_v_me': {invite}
}

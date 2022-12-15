//Action control function handlers
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//- Consolidate code in user ticket and tally invitation
//- 
const { Log } = require('wyclif')
var log = Log('cont-tally')
var qr = require('qr-image')
var errCode = function(view, code) {return {code: '!' + view + '.' + code}}

// ----------------------------------------------------------------------------
function invite(info, cb, resource) {	//Build a tally invitation: uses express server for included svg resource
  let {data, view, resPath, db} = info
    , {keys, options} = (data ? data : {})
    , key = ((keys && keys[0]) ? keys[0] : {})
    , error
log.debug('Calling invite:', JSON.stringify(data))

  if (resource) return false			//No support for http calls
  let content = ''
    , sql = 'insert into mychips.tokens_v_me (tally_seq, reuse) values ($1,$2) returning token, expires, chad'
  info.cache = {}
  db.query(sql, [key.tally_seq, options.reuse], (err, res) => {
log.trace('  err:', err, ' res:', res, 'rows:', res.rows ? res.rows[0] : null)

    if (info.cache.error = err) {
      log.error("Error creating tally ticket:", err)
      info.cache.error = err
      error = errCode(view, 'GTT')		//Generating tally ticket

    } else if (res.rows && res.rows.length == 1) {
      let ticket = info.cache.ticket = res.rows[0]
log.debug('  ticket:', info.cache.ticket)
      info.cache.json = JSON.stringify({ticket})

      switch (options?.format) {
        case 'qr':
          content = qr.imageSync(info.cache.json, {type:'svg'})
          break
        case 'link':
          content = [
            '<a href="',
            `mychips://tally?token=${ticket.token}&chad=${JSON.stringify(ticket.chad)}`,
            '">',
            '!' + view + '.TIN',
            '</a><p>',
            '!' + view + '.TIL',
            ': ', ticket.expires,
          ]
          break
        default:
          error = errCode(view, 'URF')		//Unknown report format
          break
      }
    }
    cb(error, content)
  })
  return (error == null)			//If false, not finished so cache report info
}

module.exports = {
  'mychips.tallies_v_me': {invite}
}

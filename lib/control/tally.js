const { Log } = require('wyclif')
var log = Log('cont-tally')
var qr = require('qr-image')
//var wyseman = require('wyseman')
var errCode = function(view, code) {return {code: '!' + view + '.' + code}}

// ----------------------------------------------------------------------------
function invite(info, cb, resource) {		//Build a tally invitation: uses express server for included svg resource
  let {data, view, resPath, db} = info
    , {keys, options} = (data ? data : {})
    , key = ((keys && keys[0]) ? keys[0] : {})
    , error
log.debug('Calling invite:', JSON.stringify(data))

  if (!resource) {				//Prepare report, build the wrapper
log.debug('  building resources:')
    let content = ''
      , query = 'insert into mychips.tokens_v_me (tally_seq, reuse) values ($1,$2) returning token, expires, chad'
    info.cache = {}
    db.query(query, [key.tally_seq, options.reuse], (err, res)=>{
log.debug('  err:', err, ' res:', res, 'rows:', res.rows ? res.rows[0] : null)

      if (info.cache.error = err) {
        log.error("Error creating tally ticket:", err)
        info.cache.error = err
        error = errCode(view, 'GTT')		//Generating tally ticket
      } else if (res.rows && res.rows.length == 1) {
        let ticket = info.cache.ticket = res.rows[0]
//Fixme: how to encode url?
          , url = `/tally?host=${ticket.host}&port=${ticket.port}&token=${ticket.token}`
log.debug('  ticket:', info.cache.ticket)
        info.cache.json = JSON.stringify({ticket})
//Fixme: get rid of english:
        content = `<div>
          <h4>Tally Ticket</h4>
          <a href="${resPath}/ticket.json">ticket.json</a>
          <a href="${resPath}/ticket.svg">ticket.svg</a>
          <a href="${url}">ticket.url</a>
          <iframe height="400" width="400" src="${resPath}/ticket.svg"/>
        </div>`
      }
      cb(error, content)
    })
    return (error == null)			//If false, not finished so cache report info
  }
  if (error || info.cache.error) return false
log.debug('  resource cache:', resource, info.cache)
  
  if (resource == 'ticket.svg') {
    let svg = qr.imageSync(info.cache.json, {type:'svg'})
    cb(null, svg)
  } else if (resource == 'ticket.json') {
    cb(null, info.cache.json)
  }
  return false
}

module.exports = {
  'mychips.tallies_v_me': {invite}
}

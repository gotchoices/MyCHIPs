//Action control function handlers
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//- 
const { log, buildContent, langCode, errCode } = require('./common')
const Ticket = require('./ticket')
var qr = require('qr-image')

// ----------------------------------------------------------------------------
function invoice(info, cb, resource) {		//Build a tally invitation: uses express server for included svg resource
  if (resource) return false			//No support for http calls
  let sql = "select cert->'chad' as chad from mychips.users_v_me"
    , {data, view, message, db} = info
    , {options} = data
    , content, error
    , {units, ref, memo} = options

log.debug('invoice:', options)
  db.query(sql, (err, res) => {
log.debug('  err:', err, ' res:', res, 'rows:', res?.rows ? res.rows[0] : null)
    if (err || !res.rows || res.rows.length != 1) {
      log.error("Error fetching chad:", err)
      error = errCode(view, 'FCH', err)
      return
    }

    let {chad} = res.rows[0]
      , {cid, agent} = chad
      , agnt = agent.length <= 12 ? agent : `${agent.slice(0, 6)}...${agent.slice(-6)}`
      , addr = [cid, agnt].join(':')
      , invoice = Object.assign({chad: {cid, agent}, units, ref, memo})
      , makeContent = function(format) {
          let url = encodeURI(`https://mychips.org/pay?chad=${addr}&units=${units}&ref=${JSON.stringify(ref)}&memo=${memo}`)
          switch (format) {
            case 'json':
              return {
                invoice, url,
                title: message('INV').title,
                message: message('INV').help,
              }
            case 'qr':
              return qr.imageSync(JSON.stringify(url), {type:'svg'})
            case 'link':
              return message('INV').help + ': ' + addr +
                '<p><a href="' + url + '">' +
                message('INV').title +
                '</a></p>'
            default:
              return message('URF').title		//Unknown report format
          }
        }
    if (!error)
      content = buildContent(options?.format, makeContent)
    cb(error, content)
  })
  return (error == null)		//If false, not finished so cache report info
}

module.exports = {
  'mychips.users_v_me': {invoice}
}

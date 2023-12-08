//Visual trading variable report generator
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//- Error code for unknown resource
//- 
const { log, buildContent, staticFile, errCode } = require('./common')
const Path = require('path')

// ----------------------------------------------------------------------------
function trade(info, cb, resource) {		//Build a graph of trading variables
  let {data, view, origin, resPath, message, langTags, db, cache} = info
    , {keys, options} = (data ? data : {})
    , key = keys?.[0] ?? data?.key
    , error, content
  if (!cache) cache = {}
log.debug('Calling trade:', JSON.stringify(data), resPath, resource)

  if (resource == 'trade.html' || resource == 'd3.js') {
    return staticFile(Path.join(__dirname, resource), cache.graphHTML, (err, cont) => {
//      cb(err, cache.graphHTML = cont)
      cb(err, cont)	//DEBUG
    })

  } else if (resource == 'trade.json') {
//log.debug('Fetch:', resource, key)		;cache.graphJSON=null	//DEBUG
    let tfields = ['target','bound','reward','clutch']
      , fields = 'tally_ent, tally_seq, hold_cid as hold, part_cid as part, hold_terms as terms, net, ' + tfields.join(',')
      , msgs = [null, 'direct', 'liftin', 'liftout', 'reset', 'submit']
      , seq = key.tally_seq || key
      , sql = `select ${fields} from mychips.tallies_v_me where tally_seq = $1`
    db.query(sql, [seq], (err, res) => {		log.debug('sql:', sql, key)
log.debug('  err:', err, ' res:', res, 'rows:', res?.rows ? res.rows[0] : null)
      if (err || res?.rows <= 0) return
      let row = res?.rows?.[0]
        , col = tfields.reduce((acc, key) => {	//Get field title data
            acc[key] = langTags.col[key]
            return acc
          }, {})
        , msg = msgs.reduce((acc, key) => {
            let tag = 'trade' + (key ? '.' + key : '')
            acc[tag] = langTags.msg[tag]
            return acc
          }, {})
        , lang = {col, msg}			//;log.debug('L:', JSON.stringify(langTags))
      cb(err, {row, col, msg}, keys, options)
    })
    return false
  } else if (resource) {
    cb(new Error('Unknown resource'))		//Fixme: make error code for this
    return false
  }

  let makeContent = function(format) {
    let link = origin + resPath + '/trade.html'
log.debug('  link:', link)
    switch (format) {
      case 'url':
        return link
      default:
        return `
          <div>${message('trade').title}</div>
          <div style="height:100%; margin: 0;">
            <iframe src="${link}" style="width:100%; height:96%; border: 1px solid #808080;">
            </iframe>
          </div>
        `
    }
  }

  content = buildContent(options?.format, makeContent)
log.debug('Res:', resource, 'Fmt:', options?.format)
  cb(error, content)
  return (!error)
}

module.exports = {
  'mychips.tallies_v_me': {trade}
}

//Visual balance sheet report generator
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//- 
const { log, buildContent, staticFile, errCode } = require('./common')
const Path = require('path')
//const Fs = require('fs')
//const { InitVisBS, UserVisBS } = require('../../src/visbs.js')

// ----------------------------------------------------------------------------
function graph(info, cb, resource) {		//Build a visual balance sheet for the user
  let {data, view, origin, resPath, message, db, cache} = info
    , {keys, options} = (data ? data : {})
    , key = keys?.[0] ?? data?.key
    , error, content
  if (!cache) cache = {}
log.debug('Calling graph:', JSON.stringify(data), resPath)

  if (resource == 'graph.html' || resource == 'd3.js') {
    return staticFile(Path.join(__dirname, resource), cache.graphHTML, (err, cont) => {
      cb(err, cache.graphHTML = cont)
//      cb(err, cont)	//DEBUG, no cache
    })
  } else if (resource == 'visbs.js') {
    return staticFile(Path.join(__dirname, '../../src', resource), cache.visbs, (err, cont) => {
      cb(err, cache.visbs = cont)
//      cb(err, cont)	//DEBUG, no cache
    })

  } else if (resource == 'user.json') {
log.debug('Fetch:', resource, key)		//;cache.graphJSON=null	//DEBUG
    let fields = 'id, std_name, peer_cuid, peer_agent, asset, assets, liab, liabs, net, latest, tallies'
      , sql = `select ${fields} from mychips.users_v_tallies_me`
    db.query(sql, (err, res) => {
log.debug('  err:', err, ' res:', res, 'rows:', res?.rows ? res.rows[0] : null)
      let row = res?.rows?.[0]
      cb(err, row, keys, options)
    })
    return false
  } else if (resource) {
    cb(new Error('Unknown resource'))
    return false
  }

  let makeContent = function(format) {
    let link = origin + resPath + '/graph.html'
    switch (format) {
      case 'url':
        return link
      default:
        return `
          <div>${message('graph').title}</div>
          <div style="height:100%; margin: 0;">
            <iframe src="${link}" style="width:100%; height:96%; border: 1px solid #808080;">
            </iframe>
          </div>
        `
    }
  }

log.debug('Res:', resource, 'Fmt:', options?.format)
  content = buildContent(options?.format, makeContent)
  cb(error, content)
  return (!error)
}

module.exports = {
  'mychips.users_v_me': {graph}
}

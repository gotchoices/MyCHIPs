//Render a tally agreement to a printable pdf format
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//- Caller must specify a tally primary key as: {data: {key:{tally_seq: n}}}
//- Make error code for unknown resource
//- 
const { log, buildContent, errCode } = require('./common')
const agreePDF = require('./agreepdf.js')
//const tallySQL = `select
//  tally_ent, tally_seq, part_ent, media, format, digest, comment,
//  file_fmt, file_data, file_name, file_ext
//  from mychips.file_v_part where tally_seq = $1`

function agree(info, cb, resource) {
  let {data, view, origin, resPath, message, db, cache} = info
    , {keys, options} = data
    //, key = ((keys && keys.length >= 1) ? keys[0] : {}) ?? data.key
    , key = keys?.[0] ?? data.key
    , error

  if (resource == 'agree.pdf') {		log.debug('  resource:', resource, 'cache:', cache.files)
    agreePDF(log, (error, content) => {
log.debug('Z:', error, 'c:', content)
      let headers = {
        'Content-Type': 'application/pdf',
        'Content-Disposition': 'inline; filename=' + 'TallyAgreement.pdf',
      }
      cb(error, content, headers)
    })
    return
  } else if (resource) {
    cb(new Error('Unknown resource'))		//Fixme: make error code for this
    return false
  }
  if (!cache) {
    cache = info.cache = {}
  }

  if (!key || !key.tally_seq) {		//No key given
    return false
  }
log.debug('File:', key, options)

//log.debug('Sql:', tallySQL + andHash)
//  db.query(tallySQL + andHash, parms, (err, res) => {
//    let rows = res?.rows			//;log.debug(' File res:', res)
//    if (!rows || rows.length < 1) return
//    cache.files = rows
//
//    content = buildContent(options?.format, makeContent)
//    cb(error, content)
//  })

  let makeContent = function(format) {
    let link = origin + resPath + '/agree.pdf'
log.debug('  link:', link)
    switch (format) {
      case 'url':
        return link
      default:
        return `
          <div>${message('agree').title}</div>
          <object data="${link}" style="width:100%; height:100%"</object>
        `
    }
  }

  let content = buildContent(options?.format, makeContent)
log.debug('Fmt:', options?.format)
  cb(error, content)
  return (!error)
}

module.exports = {
  'mychips.tallies_v_me': {agree}
}

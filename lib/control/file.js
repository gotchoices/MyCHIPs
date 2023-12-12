//Fetch a file object associated with a tally
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//X- Caller must specify a tally primary key as: {data: {key:{tally_seq: n}}}
//X- Caller may specify a base64url) options.digest and only that file will be returned
//X- Otherwise, all file objects found on the tally will be returned
//X- If the specified file belongs to a user hosted on the same system, we can get it from our DB
//- Otherwise, we must call the public doc server on the user's host system to get the file(s)
//- 
const { log, buildContent, errCode } = require('./common')
const tallySQL = `select
  tally_ent, tally_seq, part_ent, media, format, digest, comment,
  file_fmt, file_data, file_name, file_ext
  from mychips.file_v_part where tally_seq = $1`

function file(info, cb, resource) {
  let {data, view, origin, resPath, message, db, cache} = info
    , {keys, options} = data
    , key = keys?.[0] ?? data?.key
    , error, content

  if (resource) {			//log.debug('  resource:', resource, 'cache:', cache.files)
    let base = resource.split('.')[0]
      , file = cache?.files?.find(el => (el.digest == base))
        err = null
    content = file.file_data
//log.debug('    found:', file?.media, 'fmt:', file?.format, 'cmt:', file?.comment)
    if (file) cb(err, content)
    return
  }
  if (!cache) {
    cache = info.cache = {}
  }

  if (!key || !key.tally_seq) {		//No key given
    return false
  }
//log.debug('File:', key, options)

  let makeContent = function(format) {
    switch (format) {
      case 'json':
        return cache.files

      default:				//html: live report of all partner's files
        let chunks = []
        cache?.files?.forEach(f => {
          let link = origin + resPath + '/' + f.digest + '.' + f.file_ext
//log.debug(' file el:', link, f.format)
          if (f.part_ent) chunks.push(`
            ${f.media}; ${f.comment} <object data="${link}" type="${f.format}"></object>
          `)
        })
        return chunks.join('\n')
    }
  }

  let andHash = ''
    , parms = [key.tally_seq]
  if (options.digest) {
    andHash = ' and digest = $2'
    parms.push(options.digest)		//;log.debug(' digest:', options.digest)
  }
//log.debug('Sql:', tallySQL + andHash)
  db.query(tallySQL + andHash, parms, (err, res) => {
    let rows = res?.rows			//;log.debug(' File res:', res)
    if (!rows || rows.length < 1) return
    cache.files = rows

    content = buildContent(options?.format, makeContent)
    cb(error, content)
  })

  return (options?.format != 'json')		//keep cache for html reports
}

module.exports = {
  'mychips.tallies_v_me': {file}
}

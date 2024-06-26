//Manages interactive contract editor in wylib web UI
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//- Consolidate to share code between reports
//- 
const { log, errCode } = require('./common')
var Format = require('pg-format')
const Stringify = require('json-stable-stringify')
const Hash = require('hash.js')

// ----------------------------------------------------------------------------
function edit(info, cb, resource) {		//Open a contract document editor
  let {data, view, origin, resPath, db} = info
    , {keys, options, request} = data
    , key = keys?.[0] ?? data?.key
    , error, whereList = [], qParms = [], parmIdx, sql, sections
    , schTab = view.split('.').map(el=>Format.ident(el)).join('.')
log.debug('Edit keys:', JSON.stringify(keys), 'options:', options, 'request:', request)

  if (resource) {		//User clicking on a resource link
    let uri = Buffer.from(resource, 'base64url').toString()
log.debug('Contract res:', uri)
    return
  }

  if (!keys) {						//No key given
    return false
  } else if (!Array.isArray(keys) || keys.length != 1) {
    error = errCode(view, 'TMK')			//Too few/many keys
  } else if (!key.host || !key.name || key.version == null || !key.language) {
    error = errCode(view, 'IDK')			//Invalid document key
  }
  parmIdx=1; Object.keys(key).forEach(f=>{
    whereList.push(Format.ident(f) + ' = $' + parmIdx++)
    qParms.push(key[f])
  })

  if (!error && !request) {				//Initial run
    sql = `select json from ${schTab} where ` + whereList.join(' and ')
log.debug('edit query:', sql, qParms)
    db.query(sql, qParms, (err, res)=>{
      if (err) log.error("Error fetching contract:", error = err)
      else if (!res.rows || res.rows.length != 1) {
        error = errCode(view,'ILR')		//Illegal rows
log.debug('  got sections:', res.rows[0], typeof res, res.rows[0])
      } else {
        data = res.rows[0].json
      }
log.debug('eq:', data, 'rp:', resPath)
      cb(error, Object.assign({resource: origin + resPath}, data))
    })
  } else if (!error && request == 'update') {
log.debug('  update:', options)
    sql = `update ${schTab} set sections = ${'$'+parmIdx++} where ` + whereList.join(' and ')
    qParms.push(options)
log.debug('  query:', sql, qParms)
//    db.query(sql, qParms, (err, res)=>{
//      if (err) log.error("Error updating contract:", error = err)
//      cb(error)
//    })
  } else if (!error) {
    error = errCode(view,'UNC')
  }
  if (error) cb(error)
  return true
}

// ----------------------------------------------------------------------------
function publish(info, cb, resource) {		//Open a contract document editor
  let {data, view, db} = info
    , {keys, options, request} = data
    , key = keys?.[0] ?? data.key
    , error, whereList = [], qParms = [], parmIdx, sql, sections
    , schTab = view.split('.').map(el=>Format.ident(el)).join('.')
log.debug('Publish:', keys, 'options:', options, 'request:', request)

  if (!keys || !Array.isArray(keys) || keys.length != 1) {
    error = errCode(view,'TMK')			//Too many keys
  } else if (!key.host || !key.name || key.version == null || !key.language) {
    error = errCode(view,'IDK')			//Invalid document key
  }
  parmIdx=1; Object.keys(key).forEach(f=>{
    whereList.push(Format.ident(f) + ' = $' + parmIdx++)
    qParms.push(key[f])
  })

  sql = `select json from ${schTab} where ` + whereList.join(' and ')
log.debug('Publish query:', sql, qParms)
  db.query(sql, qParms, (err, res)=>{
    if (err) log.error("Error fetching contract:", error = err)
    else if (!res.rows || res.rows.length != 1) {
      error = errCode(view,'ILR')
    } else {
      let json = res.rows[0].json
log.debug('  got json:', json)
      delete json.digest
      let digest = Hash.sha256().update(Stringify(json)).digest('hex')
      qParms.push(digest)
      sql = `update ${schTab} set published = current_date, digest = $${parmIdx++} where ` + whereList.join(' and ')
log.debug('  query:', sql, qParms)
      db.query(sql, qParms, (err, res)=>{
        if (err) log.error("Error publishing contract:", error = err)
        else cb(error, digest)
      })
    }
  })


  return true
}

module.exports = {
  'mychips.contracts_v': {edit, publish}
}

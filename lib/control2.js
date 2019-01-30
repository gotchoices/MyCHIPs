//Action control function handlers
// ----------------------------------------------------------------------------
var log = require('./logger')('control1')
var wyseman = require('wyseman')
var Format = require('pg-format')

// ----------------------------------------------------------------------------
function edit(info, cb) {			//Open a contract document editor
  let {data, view, db} = info
    , {keys, options, command} = data
    , key = ((keys && keys.length >= 1) ? keys[0] : {})
    , error, whereList = [], qParms = [], parmIdx, sql, sections
    , schTab = view.split('.').map(el=>Format.ident(el)).join('.')
log.debug('Edit keys:', keys, 'options:', options, 'command:', command)

  if (!keys || !Array.isArray(keys) || keys.length != 1) {
    error = view + '!TMK'			//Too many keys
  } else if (!key.title || !key.author || key.version == null || !key.language) {
    error = view + '!IDK'			//Invalid document key
  }
  parmIdx=1; Object.keys(key).forEach(f=>{
    whereList.push(Format.ident(f) + ' = $' + parmIdx++)
    qParms.push(key[f])
  })

  if (!command) {				//Initial run
    sql = `select sections from ${schTab} where ` + whereList.join(' and ')
log.debug('  query:', sql, qParms)
    db.query(sql, qParms, (err, res)=>{
      if (err) log.error("Error fetching contract:", error = err.message)
      else if (!res.rows || res.rows.length != 1) {
        error = view + '!ILR'			//Illegal rows
log.debug('  got sections:', res.rows[0], typeof res, res.rows[0])
      } else {
        sections = res.rows[0].sections
      }
      cb({content:{text:sections,title:key.title}, error})
    })
  } else if (command == 'update') {
log.debug('  update:', options)
    sql = `update ${schTab} set sections = ${'$'+parmIdx++} where ` + whereList.join(' and ')
    qParms.push(options)
log.debug('  query:', sql, qParms)
    db.query(sql, qParms, (err, res)=>{
      if (err) log.error("Error updating contract:", error = err.message)
      cb({error})
    })
  } else {
    error = view + '!UNC'
  }
  if (error) return false
}

// ----------------------------------------------------------------------------
function publish(info, cb, resource) {		//Open a contract document editor
  let {data, resPath, db} = info
    , {keys, options} = data
    , error
log.debug('Calling publish', keys, options, resPath)

//  if (keys.length < 1)
//    error = 'No user ID specified'
//  else if (keys.length > 1)
//    error = "Too many user ID's specified"
//  else if (!userId)
//    error = "Invalid user ID"
  return true
}

module.exports = {
  'mychips.contracts_v': {edit, publish}
}

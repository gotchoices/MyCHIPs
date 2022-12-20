//Generate a ticket from the database
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//- 
var { log, errCode } = require('./common')

// ----------------------------------------------------------------------------
module.exports = function ticket(info, sql, keyFields, optFields, cb) {
  let {data, view, resPath, db} = info
    , {keys, options} = (data ? data : {})
    , key = ((keys && keys[0]) ? keys[0] : {})
    , error, ticket
    , parms = keyFields.map(f => key[f]).concat(
        optFields.map(f => options[f])
      )
log.debug('Calling ticket', sql, parms)

  if (!keys || !Array.isArray(keys) || keys.length != 1)
    error = errCode(view, 'TMK')		//Too few/many keys

  db.query(sql, parms, (err, res) => {
log.debug('  err:', err, ' res:', res, 'rows:', res?.rows ? res.rows[0] : null)

    if (err) {
      log.error("Error creating ticket:", err)
      error = errCode(view, 'GTK', err)		//Generating Ticket

    } else if (res.rows && res.rows.length == 1) {
      ticket = res.rows[0]
    }
    cb(error, ticket, keys, options)
  })
  return (error == null)		//If false, not finished so cache report info
}

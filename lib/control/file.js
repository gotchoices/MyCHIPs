//Fetch a file object associated with a tally
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//- Caller must specify a tally sequence number (can only request objects from user's own tallies)
//- Caller may specify a file hash and only that file will be returned
//- Otherwise, all file objects found on the tally will be returned
//-
//- If the specified file belongs to a user hosted on the same system, we can get it from our DB
//- Otherwise, we must call the public doc server on the user's host system to get the file(s)
//- 
//- 
const { log } = require('./common')
//const Sharp = require('sharp')

// ----------------------------------------------------------------------------

function file(info, cb, resource) {
  if (resource) return false			//No support for http calls

  let {data, view, db} = info
    , {fields, options} = data
    , error, content
//    , max = options?.max ?? 512
//    , fData = fields?.file_data
//    , fileData = Buffer.isBuffer(fData) ? fields.fData :	//Make sure we have a buffer type
//      (typeof fData == 'object' && fData.type == 'Buffer') ? Buffer.from(fData.data) : null
      
log.debug('File:', max, Object.keys(fields), options)

  return false
}

module.exports = {
  'mychips.tallies_v_me': {file}
}

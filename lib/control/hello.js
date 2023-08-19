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

function hello(info, cb, resource) {
  let {data, view, origin, resPath, message, db, cache} = info
  let {keys, options} = data
  let key = keys?.[0] ?? data.key
  let error, content

  content = "Hello World Eh?"
  cb(error, content)

  return (options?.format != 'json')		//keep cache for html reports
}

module.exports = {
  'mychips.tallies_v_me': {hello}
}

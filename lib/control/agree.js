//Render a tally agreement contract to a printable pdf format
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//- Caller must specify a tally primary key as: {data: {key:{tally_seq: n}}}
//- Make error code for unknown resource
//- 
const { log, buildContent, errCode } = require('./common')
const contractSQL = `select mychips.contract_mat(json) as json 
		from mychips.contracts_v where rid = $1`
const BuildPDF = require('./buildpdf.js')
var buildPDF = new BuildPDF(log)

function agree(info, cb, resource) {
  let {data, view, origin, resPath, message, db, cache} = info
    , {keys, options} = data
    , key = keys?.[0] ?? data.key
    , error

  if (resource == 'agree.pdf') {		log.debug('  resource:', resource, 'cache:', cache.files)
    buildPDF.contract(cache.json, (error, content) => {
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
log.debug('Agree:', key, options)

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

//let parms = ['GLJJEMbxfH7caHcNEhNqR7H4yDhsPpBe9vJuxCdTonrB']
let parms = ['BqQZqh3xUtye3JnAKhwdMrCMHem3vX67gV3UevGBr4pE']	//Tally
//let parms = ['9vdx9fmL2XQeyLKWaMQjNHzxPv5QTeZ1PZJDSdr3Rqi8']	//Free
log.debug('Sql:', contractSQL, parms)
  db.query(contractSQL, parms, (err, res) => {
    let row = res?.rows?.[0]			//;log.debug(' Contract res:', res)
    cache.json = row.json

    content = buildContent(options?.format, makeContent)
    cb(error, content)
  })

  return (!error)
}

module.exports = {
  'mychips.tallies_v_me': {agree}
}

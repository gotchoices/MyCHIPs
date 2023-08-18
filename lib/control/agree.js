//Render a tally agreement contract to a printable pdf format
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//- Caller must specify a tally primary key as: {data: {key:{tally_seq: n}}}
//- Make error code for unknown resource
//- 
const { log, buildContent, errCode } = require('./common')
const { Language } = require('wyseman')
const BuildPDF = require('./buildpdf.js')
const tallySQL = `select json as tally, 
        tally_uuid, version, comment, digest::text, tally_date::text, 
        mychips.contract_formal(contract,true) as contract
        from mychips.tallies_v_me where tally_seq = $1`

function agree(info, cb, resource) {
  let {data, view, origin, resPath, message, db, cache, langTags, language} = info
    , {keys, options} = data
    , key = keys?.[0] ?? data?.key
    , error

  if (resource == 'agree.pdf') {		//log.debug('  resource:', resource, 'cache:', cache.files)
    let pdf = new BuildPDF(log)
    pdf.tally(cache).render((error, content) => {	//log.debug('Z:', error, 'c:', content)
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
    cache = info.cache = {langTags}
  }

  if (!key || !key.tally_seq) {		//No key given
    return false
  }
//log.debug('Agree:', key, options)

  let makeContent = function(format) {
    let link = origin + resPath + '/agree.pdf'		//;log.debug('  link:', link)
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

//log.debug('Sql:', tallySQL, key)
  db.query(tallySQL, [key.tally_seq], (err, res) => {
    let row = res?.rows?.[0]			//;log.debug(' Tally row:', row)
    if (err)
      cb(err)

    else if (!row?.contract)
      cb(errCode(view, 'CNF'), key.tally_seq)		//Contract not found

    else Language.viewData(language, 'mychips.users_v_me', userLang => {
      Object.assign(cache, row, {userLang: userLang})	//What we will need for the report
  
      content = buildContent(options?.format, makeContent)
      cb(err, content)
    })
  })

  return (!error)
}

module.exports = {
  'mychips.tallies_v_me': {agree}
}

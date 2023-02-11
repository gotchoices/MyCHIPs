//Visual balance sheet report
//Copyright MyCHIPs.org; See license in root of this package
// ----------------------------------------------------------------------------
//TODO:
//- 
const { log, buildContent } = require('./common')
const Fs = require('fs')
const Path = require('path')
var graphHTML

// ----------------------------------------------------------------------------
function graph(info, cb, resource) {		//Build a visual balance sheet for the user
  let {data, view, resPath, lang} = info
    , {keys, options} = (data ? data : {})
    , key = ((keys && keys[0]) ? keys[0] : {})
    , error, content
log.debug('Calling graph:', JSON.stringify(data))

  if (resource == 'graph.html') {
log.debug('Fetch graph resource:', resource)
    if (graphHTML)			//Have we fetched before
      cb(error, graphHTML)		//then return it
    else				//else fetch it now
      Fs.readFile(Path.join(__dirname, resource), 'utf8', (err, html) => {
log.debug('HTML:', html)
        cb(err ?? error, graphHTML = html)
      })
    return false
  }

  let makeContent = function(format) {
    let link = resPath + '/graph.html'
    switch (format) {
      case 'html':
        return `
          ${lang.message('graph').title}<div style="height:100%; margin: 0;">
            <iframe src=${link} style="width:100%; height:96%; border: 1px solid #808080;">
            </iframe>
          </div>
        `
      case 'url':
        return link
      default:
        return lang.message('URF').title		//Unknown report format
    }
  }
  content = buildContent(options?.format, makeContent)
  cb(error, content)
            
  return (!error)
}

module.exports = {
  'mychips.users_v_me': {graph}
}

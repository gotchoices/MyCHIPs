//Launch http service to serve contract documents to the browser
//Copyright WyattERP.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//-
const	Express		= require('express')
const	Http		= require('http')
const	Https		= require('https')
const	Path		= require('path')
const	Url		= require('url')
const	Favicon		= require('serve-favicon')
const	QueryString	= require('querystring')
const	Wylib		= require.resolve('wylib/src')	//Not babelized version
const { dbClient }	= require('wyseman')
const { Log }		= require('wyclif')
const	Viewer		= 'contract.html'
const	DefConfig	= {
  docPort:	80,
  expApp:	Express(),
  docPath:	'*',
}
const	RedirDoc	= `
  <!DOCTYPE html>
  <html>
    <head>
      <meta http-equiv="refresh" content="0; url=%U"/>
    </head>
    <body>
     <p>Attempting redirect to: <a href="%U">fetch document.</a></p>
    </body>
  </html>`					//Document to redirect to URL with paramaterized query

module.exports = function(servConfig, dbConfig) {
  let d = Object.assign({}, DefConfig, servConfig)
    , dbConf = {log: this.log}
    , favIconFile = Path.join(d.pubDir, "favicon.svg")
    , contractFile = Path.join(d.pubDir, "contract.html")
    , server = d.credentials ? Https.createServer(d.credentials, d.expApp) : Http.createServer(d.expApp)

  d.expApp.use(Express.static(d.pubDir))		//Serve static files
  d.expApp.use(Favicon(favIconFile))
  Object.assign(dbConf, dbConfig)			//Merge in any user specified database arguments
  this.db = new dbClient(dbConf)
  this.log = Log('doc')
  this.contractHtml = null
//this.log.trace("Doc Server:", d.docPort, d.docPath)

  d.expApp.get(d.docPath, (req, res)=>{
//this.log.trace("url:", req.url, req.url.slice(0,1))
    let url = Url.parse(req.url)		//Get the components of the URL
      , { pathname, query } = url
    
    if (pathname == '/json') {			//Requesting raw JSON from database
      let params = QueryString.parse(query)
        , { domain, name, version, language, digest } = params
this.log.trace("JSON request:", domain, "n:",name, "v:",version, "l:",language, "d:",digest)
      if (!domain || !name || !version || !language) return
      
      this.db.query("select json from mychips.contracts_v where domain = $1 and name = $2 and version = $3 and language = $4", [domain, name, version, language], (e,r)=>{
        if (e) {this.log.error('Fetching document:', e.message); return}
        let resp = r && r.rows ? r.rows[0] : ''
          , data = resp.json
this.log.trace("DB doc data:", data)
        res.end(JSON.stringify(data))
      })

    } else {					//Requesting a document in its native URL format
      let [ pname, version, language ] = QueryString.unescape(pathname).split('-')
        , parms = QueryString.parse(query)
        , name = pname.slice(0,1) == '/' ? pname.slice(1) : pname
        , { domain, digest } = parms
        , host = req.get('host')
      if (!domain) domain = host.split(':')[0]		//If no domain in query, use the host we're connecting to
this.log.trace("Native doc request:", domain, "n:",name, "v:",version, "l:",language, "d:",digest)

      let params = {domain,name,version,language,digest}
        , qString = Object.keys(params)
          .map(k => encodeURIComponent(k) + '=' + encodeURIComponent(params[k]))
          .join('&')
        , newUrl = req.protocol + '://' + host + '/' + Viewer + '?' + qString

//this.log.trace("Url:", newUrl)
      res.end(RedirDoc.replace(/%U/g, newUrl))
    }
  })

  server.listen(d.docPort)
this.log.debug("Serving documents at port:", d.docPort)
  return d.expApp
}

//Launch http services for CHIP Service Provider home page
//Copyright MyCHIPS.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//-
const	Express		= require('express')
const	Http		= require('http')
const	Https		= require('https')
const	Path		= require('path')
const	Url		= require('url')
const	FavIcon		= require('serve-favicon')
const { dbClient }	= require('wyseman')
const { Log }		= require('wyclif')
const	NodeMailer	= require('nodemailer')
const	CodeSize	= 1e9			//Random connection code space
const	defSmtpPort	= 25
const	DefConfig	= {
  httpPort: 80,
  httpsPort: 443,
  expApp: Express(),
  pubDir: Path.join(__dirname, '..', 'pub'),
  homeDir: Path.join(__dirname, '..', 'pub', 'home'),
}

module.exports = class {
  constructor(config, dbConfig) {
    this.conf = Object.assign({}, DefConfig, config)
    this.expApp = this.conf.expApp		//Accessed by external modules
    this.log = this.conf.log || Log('genweb')
this.log.trace("General Web Services:", this.conf.httpPort, this.conf.httpsPort, this.conf.homeDir)
    this.confirms = {}				//Pending confirmations
    
    this.db = new dbClient(Object.assign({log: this.log}, dbConfig))

    if (Boolean(this.conf.httpPort)) {	// Redirect any traffic from port 80
      this.httpServer = Http.createServer((req, res) => {
        res.writeHead(301, { "Location": "https://" + req.headers['host'] + req.url })
        res.end()
      })
      this.httpServer.listen(this.conf.httpPort)
    }
  
    if (Boolean(this.conf.httpsPort)) {
      this.httpsServer = Https.createServer(this.conf.credentials, this.expApp)
  
      if (this.conf.favIconFile)
        this.expApp.use(FavIcon(Path.join(this.conf.pubDir, this.conf.favIconFile)))
      this.expApp.use(Express.static(this.conf.homeDir))
      this.expApp.use(Express.urlencoded({extended: true}))

      this.expApp.post('/submit/*', (req,res) => this.procSubmit(req,res))
      this.expApp.get('/confirm/:code', (req, res) => this.procConfirm(req,res))
      this.httpsServer.listen(this.conf.httpsPort)
    }	//if
  }	//constructor

  procSubmit(req, res) {		//On initial submission from signup/ticket form
    let code, body = req.body
      , reqType = req.params[0]
      , emailData = this.conf.email[reqType]
this.log.debug("CSP post b", body)
this.log.trace("CSP post p", req.params, 'Info:', JSON.stringify(body.info))
    if (!body.ent_name || !body.email || !body.born_date || !body.tos || !body.origin)	//Fail quietly
      return
    body.reqType = reqType			//So proConfirm knows the request type
    do {					// Make a unique confirmation code
      code = Math.round(Math.random() * CodeSize)
    } while (this.confirms[code])		//;this.log.debug("  code", code)
    this.confirms[code] = body

    setTimeout(() => {				//Confirmation code only lasts so long
      delete this.confirms[code]		//;this.log.debug("  Deleting code:", code)
    }, this.conf.linkExpire)

    let url = new URL(body.origin)
      , link = `<a href=${body.origin}confirm/${code}>${emailData?.confirm}</a>`
      , expMessage = emailData.expire.replace('%', this.conf.linkExpire / 60000)
this.log.trace("  Smtp:", this.conf.smtpHost, this.conf.smtpPort)
this.log.debug("  Email:", body.email, emailData?.subject, emailData?.html, link)
    this.sendEmail({
      from: 'no-repy@' + url.hostname,
      to: body.email,
      subject: emailData?.subject,
      text: emailData?.subject,
      html: emailData?.html + link + expMessage
    }, () => {
      res.writeHead(301, { "Location": "https://" + req.headers['host'] + '/confirm.html' })
      res.end()
    })
  }

  sendEmail(email, cb) {
this.log.debug("  Smtp:", this.conf.smtpHost, this.conf.smtpPort)
    NodeMailer.createTransport({
      host: this.conf.smtpHost || url.hostname,
      port: this.conf.smtpPort || defSmtpPort,
      tls: {rejectUnauthorized: false}
    }).sendMail(email, (err, info) => {
this.log.debug("SMTP Done:", err, 'Info:',  info)
      if (!err) cb()
    })
  }

  procConfirm(req, res) {		//On user confirming first link
this.log.debug("CSP Confirm:", req.params)
    let code = req.params?.code
      , confirm = code ? this.confirms[code] : null
    if (!code || !confirm) return
// let carr=Object.keys(this.confirms); code=carr[carr.length-1]; confirm=this.confirms[code]	//For testing, & Comment line above
this.log.debug("CSP Confirm Found:", confirm)

    this.db.query('select token,expires,host,port,token_ent as user from mychips.ticket_login($1::jsonb)', [confirm], (e,r)=>{
      if (e) {this.log.error('Processing connection ticket:', e.message); return}
      let ticket = r && r.rows ? r.rows[0] : {}
        , deep = `mychips://connect/?host=${ticket.host}&port=${ticket.port}&token=${ticket.token}&user=${ticket.user}`
this.log.debug("Ticket response:", ticket)
      if (!ticket || !ticket.token) return
      
this.log.debug("Ticket ready:", deep, confirm)
//      this.sendEmail({
//        from: 'no-repy@',		// + url.hostname,
//        to: confirm.email,
//        subject: confirm.subject,
//        text: confirm.subject,
//        html: confirm.html	//	 + link + expMessage
//      }, () => {
//        res.writeHead(301, { "Location": "https://" + req.headers['host'] + '/ticket.html' })
//        res.end()
//      })
    })
  }
  
  procRegister(data) {
this.log.debug("Register:", data)
//    this.db.query("select json from mychips.contracts_v where domain = $1 and name = $2 and version = $3 and language = $4", [domain, name, version, language], (e,r)=>{
//      if (e) {this.log.error('Fetching document:', e.message); return}
//      let resp = r && r.rows ? r.rows[0] : ''
//        , data = resp ? resp.json : null
//this.log.debug("DB doc data:", data)
//      if (data) res.end(JSON.stringify(data))
//    })
  }
  
  procReissue(body) {
this.log.debug("Reissue:", body)
    let query = `select id, ent_name, fir_name, born_date from mychips.users_v u where exists (
      select comm_seq from base.comm_v where comm_ent = u.id and comm_type = email not comm_inact and comm_spec = $1
    )`
//    this.db.query(query, [body.email], (e,r)=>{
//      if (e) {this.log.error('Locating user for reissue:', e.message); return}
//      let resp = r && r.rows ? r.rows[0] : ''
//        , data = resp ? resp.json : null
//this.log.debug("Restore data for:", data)
//      if (data) res.end(JSON.stringify(data))
//    })
  }

  close() {
    if (this.httpServer) this.httpServer.close()
    if (this.httpsServer) this.httpsServer.close()
  }
}	//class

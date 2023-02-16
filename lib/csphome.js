//Launch http services for CHIP Service Provider home page
//Copyright MyCHIPS.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//-
const	Express		= require('express')
const	Http		= require('http')
const	Https		= require('https')
const	Path		= require('path')
const	Fs		= require('fs')
const	Url		= require('url')
const	FavIcon		= require('serve-favicon')
const { dbClient }	= require('wyseman')
const { Log }		= require('wyclif')
const	NodeMailer	= require('nodemailer')
const	Qr		= require('qr-image')
const	CodeSize	= 1e9			//Random connection code space
const	defSmtpHost	= 'localhost'
const	defSmtpPort	= 25
const	defAgentFile	= Path.join(__dirname, '../pki/local/default_agent')
const	localAgentInfo	= Path.join(__dirname, '../local/getAgentInfo.js')
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
    
    if (Fs.existsSync(localAgentInfo)) {		//If site provides an agent assigner
      this.getAgentInfo = require(localAgentInfo)	//overwrite locally defined assigner
this.log.trace("Found local agent assigner:")
    } else {
      this.defAgent = {}
      Fs.readFile(defAgentFile, (err, keyData) => {	//We will assign all to the default
        if (err) {this.log.error("Can't access default agent key file:", defAgentFile); return}
        try {
           this.defAgent = JSON.parse(keyData.toString())
        } catch (e) {
          this.log.error("Can't parse key data in:", defAgentFile, e.message)
        }
this.log.trace("Default Agent:", this.defAgent)
      })
    }

this.log.debug("DKIM Key:", this.conf.dkimKey, this.conf.dkimSelect)
    if (this.conf.dkimKey) {				//Is there a DKIM encryption key file
      this.dkim = {		//domainName, privateKey set just in tim
        keySelector: this.conf.dkimSelect || 'mychips',
      }
      Fs.readFile(this.conf.dkimKey, (err, keyData) => {	//Hope this fires before any emails have to go out
        if (err) {this.log.error("Can't access dkim key file:", this.conf.dkimKey); return}
        this.dkim.privateKey = keyData		//;this.log.trace("DKIM Data:", keyData)
      })
    }
  }	//constructor

  getAgentInfo(info) {			//Default function to assign user to an agent
this.log.debug('getAgentInfo info:', info, this.defAgent)
    return {peer_agent:this.defAgent.key.x, peer_host: this.defAgent.host, peer_port: this.defAgent.port}
  }

  sendEmail(origin, contents, cb) {
this.log.trace("  Mail:", this.conf.smtpHost, this.conf.smtpPort, this.conf.dkim)
    if (!this.transport) {			//Build transport just in time
      let url = new URL(origin)
        , addr = this.conf?.emailData?.from || 'no-reply'
      this.fromAddress = addr + '@' + url.hostname	//First email sent establishes our from domain
      if (this.dkim)
        this.dkim.domainName = url.hostname
//this.log.debug("  Mail dkim:", this.dkim)
      this.transport = NodeMailer.createTransport({
        host: this.conf.smtpHost || defSmtpHost,
        port: this.conf.smtpPort || defSmtpPort,
        tls: {rejectUnauthorized: false},
        dkim: this.dkim
      })
    }
    contents.from = this.fromAddress			//Add from address
    this.transport.sendMail(contents, (err, info) => {
this.log.trace("SMTP Done:", err, 'Info:',  info)
      if (!err) cb()
    })
  }

  procSubmit(req, res) {		//On initial submission from signup/ticket form
    let code, body = req.body
      , reqType = req.params[0]
      , emailData = this.conf.emailData[reqType]
this.log.debug("CSP post b", body)
this.log.trace("CSP post p", req.params, 'Info:', JSON.stringify(body.info))
    if (   !body.ent_name
    	|| !body.email
    	|| !body.born_date
    	|| !body.tos 
    	|| !body.origin
    	|| body.address				//Honeypot form field
    ) return					//Fail quietly
    body.reqType = reqType			//So proConfirm knows the request type
    do {					// Make a unique confirmation code
      code = Math.round(Math.random() * CodeSize)
    } while (this.confirms[code])		//;this.log.debug("  code", code)
    if (reqType == 'register')			//Merge in agent,host,port information
      body = Object.assign(body,this.getAgentInfo(body))
    this.confirms[code] = body
this.log.debug("CSP body:", body)

    setTimeout(() => {				//Confirmation code only lasts so long
      delete this.confirms[code]		//;this.log.debug("  Deleting code:", code)
    }, this.conf.emailData.expire * 1000)

    let url = new URL(body.origin)
      , msg1 = emailData.html.replace('%L',`<a href=${body.origin}confirm/${code}>${emailData.link}</a>`)
      , msg2 = msg1.replace('%T', this.conf.emailData.expire / 60)
this.log.trace("  Smtp:", this.conf.smtpHost, this.conf.smtpPort)
this.log.debug("  Email:", body.email, emailData?.subject, emailData?.html)
    this.sendEmail(body.origin, {
      to: body.email,
      subject: emailData?.subject,
      text: emailData?.subject,
      html: msg2
    }, () => {
      res.writeHead(301, { "Location": "https://" + req.headers['host'] + '/confirm.html' })
      res.end()
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
        , emailData = this.conf.emailData.ticket
        , deep = `https://mychips.org/connect?host=${ticket.host}&port=${ticket.port}&token=${ticket.token}&user=${ticket.user}`
        , msg1 = emailData.html.replace('%L',`<a href=${deep}>${emailData.link}</a>`)
        , msg2 = msg1.replace('%T', ticket.expires)
        , qrImage = Qr.imageSync(JSON.stringify({ticket}), {type:'png'} )

this.log.debug("Ticket:", ticket, deep, confirm)
      if (ticket && ticket.token) {
        this.sendEmail(confirm.origin, {
          to: confirm.email,
          subject: emailData.subject,
          text: emailData.subject,
          html: msg2,
          attachments: [{
            filename: 'ticket.gif',
            content: qrImage,
          }]
        }, () => {
          res.writeHead(301, { "Location": "https://" + req.headers['host'] + '/ticket.html' })
          res.end()
        })
      } else {
        res.writeHead(301, { "Location": "https://" + req.headers['host'] + '/error.html' })
        res.end()
      }
    })
  }
  
  close() {
    if (this.httpServer) this.httpServer.close()
    if (this.httpsServer) this.httpsServer.close()
  }
}	//class

const Fs = require('fs')
const Path = require('path')
const conFile = '../local/config.js'
const d = Fs.existsSync(conFile) ? require(conFile) : {}

module.exports = {
  dbHost:	d.dbHost	|| process.env.MYCHIPS_DBHOST,
  dbPassword:	d.dbPassword	|| process.env.MYCHIPS_DBPASSWORD,
  dbName:	d.dbName	|| process.env.MYCHIPS_DBNAME		|| 'mychips',
  dbPort:	d.dbPort	|| process.env.MYCHIPS_DBPORT		|| 5432,
  dbAdmin:	d.dbAdmin	|| process.env.MYCHIPS_DBADMIN		|| 'admin',
  uiPort:	d.uiPort	|| process.env.MYCHIPS_UIPORT		|| 1024,
  clifPort:	d.clifPort	|| process.env.MYCHIPS_WSPORT		|| parseInt(process.env.MYCHIPS_UIPORT) + 1 || 1025,
  clifNP:	d.clifNP	|| process.env.MYCHIPS_NPPORT		|| 10240,
  httpPort:	d.httpPort	|| process.env.MYCHIPS_HTTPPORT		|| 8000,
  httpsPort:	d.httpsPort	|| process.env.MYCHIPS_HTTPSPORT	|| 8443,
  webKey:	d.webKey	|| process.env.MYCHIPS_WEBKEY		|| Path.join(__dirname, '../pki/local/web-%.key'),
  webCert:	d.webCert	|| process.env.MYCHIPS_WEBCERT		|| Path.join(__dirname, '../pki/local/web-%.crt'),
  agentKey:	d.agentKey	|| process.env.MYCHIPS_AGENTKEY		|| Path.join(__dirname, '../pki/local/default_agent'),
  dbUserKey:	d.dbUserKey	|| process.env.MYCHIPS_DBUSERKEY	|| Path.join(__dirname, '../pki/local/data-user.key'),
  dbUserCert:	d.dbUserCert	|| process.env.MYCHIPS_DBUSERCERT	|| Path.join(__dirname, '../pki/local/data-user.crt'),
  dbAdminKey:	d.dbAdminKey	|| process.env.MYCHIPS_DBADMINKEY	|| Path.join(__dirname, '../pki/local/data-admin.key'),
  dbAdminCert:	d.dbAdminCert	|| process.env.MYCHIPS_DBADMINCERT	|| Path.join(__dirname, '../pki/local/data-admin.crt'),
  dbCA:		d.dbCA		|| process.env.MYCHIPS_DBCA		|| Path.join(__dirname, '../pki/local/data-ca.crt'),

  smtpHost:	d.smtpHost	|| process.env.MYCHIPS_SMTPHOST		|| 'localhost',
  smtpPort:	d.smtpPort	|| process.env.MYCHIPS_SMTPPORT		|| 25,
  dkimKey:	d.dkimKey	|| process.env.MYCHIPS_DKIMKEY,
  dkimSelect:	d.dkimSelect	|| process.env.MYCHIPS_DKIMSELECT	|| 'mychips',
  cspEmail:	Object.assign({
    from:      process.env.MYCHIPS_DBADMIN || 'admin',
    expire: 	5 * 60,
    register:	{
      subject:	'MyCHIPs Registration Confirmation',
      html:	"Thank you for registering for a MyCHIPs account.<p>"
                + "To continue registration, please click this link: %L within %T minutes.",
      link:	'Confirm Registration'
    },
    restore:	{
      subject:	'Request for new MyCHIPs Connection Ticket',
      html:	"A request was received to issue a new connection token for your account.<p>"
                + "If you did not initiate this, please ignore this email.<p>"
                + "If you proceed, your previous connection key (and any previous connection ticket) will be invalidated by the new connection ticket.<p>"
                + "To proceed to restore connection with a new ticket, click this link: %L with %T minutes.",
      link:	'Confirm Re-issue of Connection Ticket'
    },
    ticket:	{
      subject:	'MyCHIPs Connection Ticket',
      html:	"This is your new account connection ticket.<p>"
                + "If you have the MyCHIPs app already installed, you may use the app to scan the included QR code.  "
                + "If you are reading this email on your mobile device, you may instead just click the following link: %L.<p>"
                + "The connection ticket will only work until: %T.",
      link:	'Connect Using New Ticket'
    }
  }, d.cspEmail)
}

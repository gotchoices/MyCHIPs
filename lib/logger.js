//Manage logging for mychips
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
const log4js = require('log4js')

log4js.configure ({
  appenders: {
    tocons: { type: "console" },
    tofile: { type: "file", filename:"/var/tmp/mychips.log" },
    serious: {
      type:	"logLevelFilter", 
      level:	"WARN",
      appender:	"tofile"
    }
  },
  categories: {
    default: {appenders: ['serious', 'tocons'], level: 'trace'},
  }
});
module.exports = log4js.getLogger

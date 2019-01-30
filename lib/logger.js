//Manage logging for mychips
//Copyright MyCHIPs.org: GNU GPL Ver 3; see: License in root of this package
// -----------------------------------------------------------------------------
const LoggerToUse='winston'

// This is just logging to console and a single file right now
// Configuration seems very confusing.  Will try winston next.
if (LoggerToUse == 'log4js') {
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

// Run with NODE_DEBUG=silly to get all logging
// Levels: silly, debug, verbose, info, warn, error
} else if (LoggerToUse == 'winston') {

  const { format, createLogger, transports } = require('winston')

  const path = require('path')
  const fs = require('fs')
  const logPath = path.join('/var', 'tmp', 'mychips')
  var defaultLevel = process.env.NODE_DEBUG || 'warn'
  if (defaultLevel == 'trace') defaultLevel = 'silly'	//some standards use 'trace'
  
  if (!fs.existsSync(logPath)) fs.mkdirSync(logPath)

  module.exports = function(tag, level = defaultLevel) {
    var logFile = path.join(logPath, tag)
    var logger = createLogger({
      level: level,
      format: format.combine(
        format.label({label: tag}),
        format.colorize(),
//        format.timestamp(),
//        format.printf(info => `${info.timestamp} ${info.label}(${info.level}): ${info.message}`)
        format.printf(info => `${info.label}(${info.level}): ${info.message}`)
      ),
      transports: [new transports.File({ filename: path.join(logPath,'combined.log') })],
    })
//console.log("Adding logger:", path.join(logPath, tag))
    if (tag) {
      logger.add(new transports.File({ filename: path.join(logPath, tag) }))
    }

    function logit(level, ...args) {		//Capable of rendering objects as text
      let message = args.map(val => {
        return((typeof val) == 'object' ? JSON.stringify(val) : val)
      }).join(' ')
//console.log("Message:", message)
      logger.log({level, message})
    }
    
    //Wrappers to allow for multiple arguments:
    logger.error   = (...args) => {logit('error',   ...args)}
    logger.warn    = (...args) => {logit('warn',    ...args)}
    logger.info    = (...args) => {logit('info',    ...args)}
    logger.verbose = (...args) => {logit('verbose', ...args)}
    logger.debug   = (...args) => {logit('debug',   ...args)}
    logger.silly   = (...args) => {logit('silly',   ...args)}
    logger.trace   = (...args) => {logit('silly',   ...args)}
    
//    logger.warn("Starting Logger:------------------------------------------")
    return logger
  }
}

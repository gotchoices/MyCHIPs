//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//Test simulator model2, model3 (that need a running mongo)
const Net = require('net')
const Path = require('path')
const Child = require('child_process')
const { testLog } = require('./common')
const DDHost = 'localhost'
const DDPort = 27017
const dockName = 'mychipsTestMongo'
var log = testLog(__filename)
var dockerMongoDown = null		//command to kill docker mongo

const checkMongo = function(done) {		//Make sure we have a mongo running
  let sock = Net.connect(DDPort, DDHost, () => {
log.debug("Found Mongo at:", DDHost, DDPort)
    sock.end()
    done()
  })
  sock.on('error', e => {		//Can't connect to mongo
//log.debug("checkMongo error:", e)
    if (e.code != 'ECONNREFUSED') throw(e)
    let buildDir = Path.join(__dirname, '../..', 'build')
      , compFile = Path.join(buildDir, 'compose-mongo.yml')
      , cmd = `docker-compose -p mongo -f ${compFile}`
      , env = Object.assign({MYCHIPS_DBHOST: dockName}, process.env)
log.debug("Launching docker with compose:", cmd)
    Child.exec(cmd + ' up -d', {env}, (e,out,err) => {	//Try to launch one in docker
//log.debug("Compose result:", e)
      if (e && e.code == 127) throw "Can't find running mongo or docker-compose environment"
      if (!e) dockerMongoDown = cmd + ' down'
      done()
    })
  })
}

const cleanupMongo = function(done) {			//Take down docker mongo
//log.debug("Docker down command:", dockerMongoDown)
  if (dockerMongoDown) Child.exec(dockerMongoDown, (err, out) => {
log.debug("Taking down docker Mongo")
    dockerMongoDown = null
    done()
  })
  else done()
}

before('Check for running mongo', function(done) {
  this.timeout(10000)
  checkMongo(done)
})

require('./model2.js')
require('./model3.js')

after('Stop any docker mongo', function(done) {
  cleanupMongo(done)
})

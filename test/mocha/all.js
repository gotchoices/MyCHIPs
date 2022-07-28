//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//Run all tests in order
const { DBName, DB2Name, DBAdmin, dropDB, Schema, testLog, dbClient, checkPG, cleanupPG } = require('./common')
var log = testLog(__filename)
const dbConfig = {database:DBName, user:DBAdmin, connect:true, log, schema:Schema}

before('Check for running postgres', function(done) {
  this.timeout(10000)
  checkPG(done)
})
before('Can connect to postgres (may create DB)', function(done) {
  this.timeout(20000)
  let db = new dbClient(dbConfig, (chan, data) => {}, () => {
    db.disconnect()
    done()
  })
})

require('./sch-crypto.js')
require('./objectset.js')
require('./peernoise.js')
//require('./peercomm.js')	//Deprecated

require('./impexp.js')		//Adds users needed for other tests
require('./testusers.js')	//Run before sch-tally or tally

require('./model1.js')
require('./models.js')		//Model2/3 require mongo instance

require('./sch-tally.js')
require('./sch-chit.js')

require('./user2.js')		//Needed for testing on two DB's
require('./tally.js')
require('./chit.js')

require('./sch-path.js')
require('./sch-route.js')
require('./route.js')

require('./sch-lift.js')
require('./lift-in.js')
require('./lift.js')

//require('./schema.js')	//Re-enable after schema settles and more text fields are filled in
//require('./sch-multi.js')	//Will empty users table

/* */
after('Delete test database', function(done) {
  let dc = 2, _done = () => {if (!--dc) done()}		//dc _done's to be done
  dropDB(_done)
  dropDB(_done, DB2Name)
})

after('Stop any docker postgres', function(done) {
  cleanupPG(done)
})

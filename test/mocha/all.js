//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//Run all tests in order
const Child = require('child_process')
const { Database, Database2, DBAdmin } = require('../settings')

require('./sch-crypto.js')
require('./objectset.js')
require('./peernoise.js')
//require('./peercomm.js')	//Deprecated

require('./impexp.js')		//Adds users needed for other tests
require('./testusers.js')	//Run before sch-tally or tally
require('./sch-tally.js')
require('./sch-chit.js')

require('./user2.js')		//Needed for testing on two DB's
require('./tally.js')
require('./chit.js')

//Re-enable after consolidating users_v, peers_v?
//require('./sch-multi.js')	//Will empty users table

after('Delete test database', function() {
  Child.exec(`dropdb --if-exists -U ${DBAdmin} ${Database}`)
  Child.exec(`dropdb --if-exists -U ${DBAdmin} ${Database2}`)
})

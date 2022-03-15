//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//Run all tests in order
const { DBName, DB2Name, DBAdmin, dropDB } = require('./common')

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

require('./sch-path.js')
require('./sch-route.js')
require('./route.js')

//Yet to implement:
//require('./sch-tally.js')
//require('./tally.js')

require('./modeler1.js')

//Re-enable after schema settles and more text fields are filled in
//require('./schema.js')

//Re-enable after consolidating users_v, peers_v?
//require('./sch-multi.js')	//Will empty users table

after('Delete test database', function(done) {
  let dc = 2; _done = () => {if (!--dc) done()}		//dc _done's to be done
  dropDB(_done)
  dropDB(_done, DB2Name)
})

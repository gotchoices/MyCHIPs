//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//Run all tests in order
const Child = require('child_process')
const { Database, DBAdmin } = require('../settings')

require('./sch-crypto.js')
require('./objectset.js')
require('./peernoise.js')

require('./peercomm.js')	//Deprecated

require('./impexp.js')		//Will add users needed for peer test
require('./testusers.js')	//Must run before sch-tally or tally
require('./sch-tally.js')
require('./tally.js')

//require('./peer.js')		//Old, needs rework

//Re-enable after consolidating users_v, peers_v?
//require('./sch-multi.js')	//Will empty users table

after('Delete test database', function(done) {
  Child.exec(`dropdb --if-exists -U ${DBAdmin} ${Database}`, done)
})

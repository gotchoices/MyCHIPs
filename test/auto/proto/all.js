//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//Run all tests in order

require('../schema/dbinit.js')
require('./testusers.js')

require('./sch-tally.js')
require('./sch-chit.js')
require('./sch-pay.js')

require('./user2.js')		//Needed for testing on two DB's
require('./tally.js')
require('./chit.js')
require('./chain.js')

require('./net1.js')
require('./sch-path.js')
require('./net02.js')
//require('./sch-route.js')	//Obsolete
//require('./route.js')		//Obsolete

//require('./sch-lift.js')	//Obsolete
//require('./lift.js')		//Obsolete
//require('./lift-in.js')	//Obsolete
require('./pay.js')

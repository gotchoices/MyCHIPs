//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//Run all tests in order

require('./schema.js')		//Builds development DB objects
require('./sch-multi.js')	//Will disrupt users table contents

require('./sch-crypto.js')
require('./objectset.js')
require('./peernoise.js')
//require('./peercomm.js')	//Deprecated

require('./impexp.js')		//Adds users needed for other tests
require('./testusers.js')	//Run before sch-tally or tally

//require('./model1.js')
//require('./models.js')		//Model2/3 require mongo instance

require('./sch-tally.js')
require('./sch-chit.js')
require('./sch-pay.js')

require('./user2.js')		//Needed for testing on two DB's
require('./tally.js')
require('./chit.js')
require('./chain.js')

require('./sch-path.js')
//require('./sch-route.js')	//Obsolete
//require('./route.js')		//Obsolete

//require('./sch-lift.js')	//Obsolete
//require('./lift.js')		//Obsolete
//require('./lift-in.js')	//Obsolete
require('./pay.js')

require('./contract.js')
require('./language.js')

//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//Run all tests in order
//const { pgCheck, pgCleanup } = require('../common')

//before('Check for running postgres', function(done) {
//  this.timeout(10000)
//  return pgCheck()
//})

require('../misc/impexp')
require('../misc/testusers')
require('./model1.js')
require('./models.js')		//Model2/3 require mongo instance

/* */
//after('Delete test database', function(done) {
//  let dc = 2, _done = () => {if (!--dc) done()}		//dc _done's to be done
//  dropDB(_done)
//  dropDB(_done, DB2Name)
//})

//after('Stop any docker postgres', function(done) {
//  pgCleanup(done)
//})

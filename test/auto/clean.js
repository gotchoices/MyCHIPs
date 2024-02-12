//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//Remove test DB and any running test dockers
const { dropDB, DB2Name, pgCheck, pgCleanup } = require('./common')

it('Delete test databases', function(done) {
  let dc = 2, _done = () => {if (!--dc) done()}		//dc _done's to be done
  dropDB(_done)
  dropDB(_done, DB2Name)
})

it('Stop any docker postgres', function(done) {
  pgCleanup(done)
})
/* */

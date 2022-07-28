//Test internal lift; run after sch-lift
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- Generate/test a linear internal lift
//- 
const { dbConf, testLog, assert, getRow, dbClient } = require('./common')
var log = testLog(__filename)
const { agent1 } = require('./def-users')
var interTest = {}			//Pass values from one test to another

describe("Test internal lift generation", function() {
  var dbA

  before('Agent connection to database', function(done) {
    dbA = new dbClient(new dbConf(log), () => {
    }, ()=>{log.info("Test DB agent connection established"); done()})
  })

  it("Delete any existing lifts and lift chits, set costs -> zero", function(done) {
    let sql = `delete from mychips.chits where chit_type = 'lift';
               delete from mychips.lifts;
               update mychips.tallies set clutch = 0;`
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {done(e)})
  })

  it("Select/perform and internal lift", function(done) {
    let sql = `select mychips.lift_local(1);`
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("Q row:", row.lift_local)
      assert.equal(row.lift_local.done, 1)
      done()
    })
  })

  it("Query resulting chits", function(done) {
    let units = 9		//Whatever is available in lift path
      , chits = 6		//Known path has 3 tallies, stock & foil
      , sql = `select count(*) as chits from
               mychips.chits where units = ${units} and status = 'good' and chit_type = 'lift'`
//log.debug("Sql:", sql)
    dbA.query(sql, null, (e, res) => {if (e) done(e)
      let row = getRow(res, 0)			//;log.debug("row:", row)
      assert.equal(row.chits, chits)
      done()
    })
  })

/* */
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{		//Let it flush out before closing
      dbA.disconnect()
      done()
      }, 200)
  })
})

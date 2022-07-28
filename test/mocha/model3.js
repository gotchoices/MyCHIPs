//Test agent-based modeler 3 at a simple level; run after impexp, testusers
//Requires a running instance of mongodb
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- 
const { dbClient, dbConf, testLog, Format, assert, getRow } = require('./common')
const { host, agent0, port0 } = require('./def-users')
const ModelCont = require('../../lib/model3')
var ahoy = 'o500'		//Give him agent@host:port info
var log = testLog(__filename)

describe("Test Agent-based modeler 3", function() {
  var db, modeler

  before('Make connection to database', function(done) {
    db = new dbClient(new dbConf(log), (chan, data) => {
    }, ()=>{log.info("Test DB connection established"); done()})
  })

  it("Initialize DB", function(done) {
    let sql = `begin;
        delete from mychips.tallies;
        update mychips.users set _last_tally = 0;
        update mychips.users_v set peer_host = '${host}', peer_agent = '${agent0}', peer_port = ${port0} where user_ent = '${ahoy}';
        commit`
    db.query(sql, (e) => {if (e) done(e); done()})
  })

  it("Launch modeler", function(done) {
    let opts = {runs: 1, interval: 100, vendor:0.10, client:0.10, agent:agent0, done}
      , docConfig = {}
    this.timeout(10000)
    modeler = new ModelCont(new dbConf(log), docConfig, opts)
  })

  it("Confirm some tallys/chits created", function(done) {
    let sql = 'select count(*) as tallies, count(chits) as chits from mychips.tallies_v'
log.debug("Sql:", sql)
    db.query(sql, null, (e, res) => { if (e) done(e)	;log.debug("res:", res.rows[0])
      let row = getRow(res, 0)
      assert.ok(row.tallies > 0)
      assert.ok(row.chits > 0)
      done()
    })
  })

/* */
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{
      db.disconnect()
      done()
      }, 200)
  })
})

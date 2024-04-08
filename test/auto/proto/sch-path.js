//Test local pathway schema at a basic level; run
//After: net1
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- 
const { dbConf, testLog, Format, assert, dbClient, queryJson } = require('../common')
const log = testLog(__filename)
//const { host, port0, port1, port2, agent0, agent1, agent2 } = require('../def-users')
//const { cidu, cidd, cidN } = require('./def-path')
//var interTest = {}			//Pass values from one test to another
//var tallySql = `insert into mychips.tallies (tally_ent, tally_uuid, tally_date, tally_type, contract, hold_cert, part_cert, hold_sig, part_sig, status) values (%L,%L,%L,%L,%L,%L,%L,%L,%L,'open') returning *`
//var chitSql = `insert into mychips.chits (chit_ent, chit_seq, chit_uuid, units, signature, reference, status) select %L,%s,%L,%s,%L,%L,'good'`
//var agree = {domain:"mychips.org", name:"test", version:1}
//var users = 4

describe("Initialize tally/path test data", function() {
  var db

  before('Connect to database', function(done) {
    db = new dbClient(new dbConf(log), null, ()=>{
      log.info("Test DB user connection established"); done()}
    )
  })

  it("Check view tallies_v_edg", function(done) {
    let sql = `update mychips.tallies set target = 3, bound = 7;
               select json_agg(s) as json from (select tally_ent,tally_seq,tally_type,inv,inp,out,target,bound,net_pc,min,max,sign
               from mychips.tallies_v_edg order by 1,2,3,4) s;`
    queryJson('tallies_v_edg', db, sql, done, 2)
  })

  it("Check view tallies_v_paths", function(done) {
    let fsets = {reward: 0.02, clutch: 0.04}		//Update both settings and cache
      , ssets = {reward: 0.04, clutch: 0.001}
      , tSql = 'update mychips.tallies set hold_sets = %L, part_sets = %L, reward = %L, clutch = %L where tally_type = %L'
      , fSql = `${Format(tSql, fsets, ssets, fsets.reward, fsets.clutch, 'foil')}`
      , sSql = `${Format(tSql, ssets, fsets, ssets.reward, ssets.clutch, 'stock')}`
      , sql = `${fSql}; ${sSql};
        select json_agg(s) as json from (
          select inp,out,circuit,min,max,bang,reward,margin,ath
            from mychips.tallies_v_paths where min > 0 and edges > 1 order by path) s;`
    queryJson('tallies_v_paths', db, sql, done, 3)
  })

/* */
  after('Disconnect from test database', function(done) {
    setTimeout(()=>{db.disconnect(); done()}, 200)
  })
})

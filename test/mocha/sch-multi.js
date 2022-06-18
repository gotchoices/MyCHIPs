//Test certain multi-table views in the schema
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
//TODO:
//- 
const { DBName, DBAdmin, testLog, Schema, assert, dropDB, dbClient } = require('./common')
var log = testLog(__filename)
const interTest = {}
const dbConfig = {database:DBName, user:DBAdmin, connect:true, log, schema:Schema}

describe("View mychips.users_v", function() {
  var db
  this.timeout(5000)		//May take a while to build database

  before('Delete test database', function(done) {
    dropDB(done)
  })

  before('Connect to (or create) test database', function(done) {
    db = new dbClient(dbConfig, (chan, data) => {}, done)
  })

  before('Delete all users if there are any', function(done) {
    let sql = 'delete from base.ent where ent_num >= 100; delete from mychips.agents;'
    db.query(sql ,(err, res) => {done()})
  })

  describe('Multiview table insert tests', function() {
    const tests = [
      {pkey:'agent', table:'mychips.agents_v',
        record:{agent:'Alone', agent_host:'mychips.net', agent_port:7201, agent_key:null, valid:false}},
      {pkey: 'id', table:'base.ent_v',record:{ent_name:'BaseOnly'}},
      {pkey: 'id', table:'base.ent_v',record:{ent_name:'BaseOnly', fir_name:'Also'}},
      {pkey: 'id', table:'mychips.users_v',
        record:{ent_name:'Chirpies',peer_cid:'zzyzy',peer_agent:'FACADE',peer_host:'localhost',peer_port:12345}},
//      {pkey: 'id', table:'mychips.users_v',
//        record:{ent_name:'Chippers',peer_cid:'zzyzz',peer_agent:'BEADEE',peer_host:'mychips.org', peer_port:54321}},
      {pkey: 'id', table:'mychips.users_v',
        record:{ent_name:'Choppies',peer_cid:'zzyzu',user_host:'mychips.com',peer_agent:'Poodle',peer_host:'mychips.org', peer_port:12345}},
    ]

    tests.forEach(({pkey, table, record}, ix) => {	//Test each record in array
      it(`Record test; ${table}; ${ix+1}`, function(done) {
        let fields = Object.keys(record)		//Get columns
          , fieldlist = fields.join(',')
          , values = Object.values(record)		//Will set columns to these values
          , fauxlist = values.map((e,x) =>('$'+(x+1))).join(',')	//$1, $2 ...
          , sql = `insert into ${table} (${fieldlist}) values (${fauxlist}) returning ${fieldlist},${pkey};`
//log.debug('Sql:', sql)
//log.debug('Values:', values)
        db.query(sql, values ,(err, res) => {if (err) {done(err)} else {
          let row = res.rows[0]				//Should just be one row
          log.info("Row:", row)
          fields.forEach(f => {assert.equal(record[f], row[f])})	//Check each field value
//log.debug('Last:', interTest.lastId, 'pkey:', pkey, 'row:', row)
          interTest.lastId = row[pkey]
          done()
        }})
      })
    })
  })

  describe('Multiview update tests', function() {
    it('Last inserted entity number', function() {
      assert.equal(interTest.lastId, 'p1003')		//ID number of our last insert
    })

    const tests = [
      {pkey:'id', pkval: 'p1000', table:'base.ent_v',record:{fir_name:'Fred'}},		//Native table
      {pkey:'id', pkval: 'p1000', table:'mychips.users_v',record:{user_port:5555, peer_cid:'bubba'}},	//Add a user record
      {pkey:'id', pkval: 'p1001', table:'mychips.users_v',record:{peer_cid:'poofie', user_host:'mychips.net'}},	//Add user and peer
      {pkey:'id', pkval: 'p1001', table:'mychips.users_v',record:{peer_agent:'ZZYZX', peer_host:'mychips.org', peer_port:22332}},	//Add agent record
      {pkey:'agent', pkval: 'FACADE', table:'mychips.agents_v',record:{agent_host:'mychips.net', agent_port:7200}},
    ]

    tests.forEach(({pkey, pkval, table, record}, ix) => {	//Test each record in array
      it(`Record test; ${table}; ${ix+1}`, function(done) {
        let fields = Object.keys(record)		//Get columns
          , entries = Object.entries(record)
          , values = Object.values(record)		//Will set columns to these values
          , asnList = fields.map((f,x) =>(f + '=$'+(x+1))).join(',')	//f1=$1, f2=$2 ...
//log.debug('Assigns:', asnList)
          , fieldlist = fields.join(',')
          , sql = `update ${table} set ${asnList} where ${pkey} = '${pkval}' returning ${fieldlist};`
//log.debug('Sql:', sql)
//log.debug('Values:', values)
        db.query(sql, values ,(err, res) => {if (err) {done(err)} else {
          let row = res.rows[0]				//Should just be one row
          log.info("Row:", row)				//;log.debug('Row:', row)
          fields.forEach(f => {assert.equal(record[f], row[f])})	//Check each field value
          done()
        }})
      })
    })
  })

  describe('Multiview delete tests', function() {
    it(`Delete user component only`, function(done) {
      let sql = `begin; 
        delete from mychips.users_v where id = 'p1001';
        select fir_name,peer_cid,user_host from mychips.users_v where id = 'p1001';
        end;`
      db.query(sql, (err, res) => {if (err) {done(err)} else {
        assert.equal(res.length, 4)		//begin, delete, select, end
        let row = res[2].rows[0]
        assert.equal(row.fir_name, 'Also')	//base record remains
//        assert.equal(row.peer_cid, 'poofie')	//peer record remains
        assert.ifError(row.user_host)		//user record gone
        done()
      }})
    })

    it(`Deleting entity/peer records`, function(done) {
      let sql = `begin; 
        delete from base.ent where ent_num >= 100;
        select count(*) from mychips.agents;
        delete from mychips.agents;
        select count(*) from mychips.agents;
        end;`					//agents should get deleted when no longer referenced
      db.query(sql, (err, res) => {if (err) {done(err)} else {
        assert.equal(res.length, 6)		//begin, delete, select, delete, select, end
        let row = res[2].rows[0]
        assert.equal(row.count, 4)		//Agents don't get auto-deleted anymore
        row = res[4].rows[0]
        assert.equal(row.count, 0)		//Now empty
        done()
      }})
    })
  })
/* */
  after('Disconnect from test database', function(done) {
    db.disconnect()
    done()
  })
});

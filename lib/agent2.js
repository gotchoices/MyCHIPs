//Improved agent-based model; Limited testing for distributed network
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
// TODO:
//X- Connect to mongodb, modeling real-world connections
//X- Populate mongo with all the people my sqlDB has in it
//X- Can upsert into agents collection
//X- Mongo stays current with postgres (if I add/delete users)
//- 
//- Multiple agent instances (one on each machine) can all access same mongodb
//- Rely on hostID for distinct server instances?
//- Do I need an ssl gateway for other hosts to reach my VM?
//- Find my transactions in mongo--not in postgres
//- My transactions should reach across databases now
//- Can I begin to model distributed lift now?
//- 
//- From version 1:
//- Currently getting two async messages for each insert (tallies and chits) and loading agents twice in a row
//- Make decisions like:
//-   Establishing new tallies (stock and foil)
//-   Closing old tallies?
//-   Paying people down-stream of me
//-   Establishing buy/sell orders
//- 

const { dbClient } = require('wyseman')
const DocClient = require('mongodb').MongoClient
const MongoOpts = { useNewUrlParser: true, useUnifiedTopology: true }
const { Log } = require('wyclif')
const uuidv5 = require('uuid/v5')
const userFields = ['id', 'std_name', 'peer_cdi', 'host_id']
const parmQuery = "select parm,value from base.parm_v where module = 'agent'"
const userQuery = `select id, std_name, peer_cdi,
	coalesce(s.stocks,0) as stocks, coalesce(s.foils,0) as foils,
	coalesce(s.partners,'{}'::text[]) as partners,
	coalesce(s.vendors,'{}'::text[]) as vendors,
	coalesce(s.clients,'{}'::text[]) as clients
	from		mychips.users_v u
	left join	mychips.tallies_v_sum s on s.tally_ent = u.id where ent_num >= 100 order by id`

module.exports = class AgentCluster {
  constructor(sqlConfig, docConfig) {
    this.log = Log('agent2')
    this.log.info('Initializing agent model controller')
    let dbConf = Object.assign({
      log: this.log,
      listen: ['mychips_agent', 'mychips_admin'],
    }, sqlConfig)

    this.parms = {interval: 1000, addclient: 0.10, addvendor: 0.20}
    this.agents = []
    this.agent = null
    this.sqlDB = new dbClient(dbConf, (channel, payload) => {	//Initialize Database connection
      this.log.debug('Async agent message from DB:', channel, payload)
      var msg = JSON.parse(payload)
      if (channel == 'mychips_agent') {
        if (msg.oper == 'UPDATE') this.sqlDB.query(parmQuery + " and mod_date >= $1", [msg.time], (e,r)=>{this.eatParms(e,r)})
      } else if (channel == 'mychips_admin') {
        this.sqlDB.query(userQuery, (e,r)=>{this.eatAgents(e,r)})
      }
    })
    this.intervalTimer = null
    this.sqlDB.query(parmQuery, (e,r)=>{this.eatParms(e,r)})
    
    let url = `mongodb://${docConfig.host}:${docConfig.port}`
    this.log.debug("Mongo url:", url)
    this.docClient = new DocClient(url, MongoOpts)
    this.docClient.connect((err, client) => {
      if (err) {this.log.error('in Doc DB connect:', err.stack); return}
      this.docDB = client.db(docConfig.database)
      let col = this.docDB.collection("agents")
      col.createIndex({peer_cdi: 1}, {unique: true})
      this.log.debug("Connected to doc DB")
      this.sqlDB.query(userQuery, (e,r)=>{this.eatAgents(e,r)})
    })
  }	//Constructor

  eatAgents(err, res) {						//Freshly load agent data from database
    if (err) {this.log.error('In query:', err.stack); return}
    if (!this.docDB) return					//Document db connected/ready
    this.log.debug('Loaded agents:', res.rows.length, res.rows)

    let col = this.docDB.collection("agents")

    col.find().toArray().then(docs => {
this.log.trace("docs:", JSON.stringify(docs))
      res.rows.forEach( row => {
        if (!docs.some(doc => {return doc.peer_cdi == row.peer_cdi})) {
          this.log.debug("Add agent:", row)
          col.insertOne(row)
        }
      })
      docs.forEach( doc => {
        if (!res.rows.some(row => {return row.peer_cdi == doc.peer_cdi})) {
          this.log.debug("Delete agent:", doc)
          col.deleteOne({_id: doc._id})
        }
      })
    }).catch(err => {
      this.error("in eatAgents:", err.stack)
    })

//    this.docDB.collection("agents").insertMany(res.rows).then(result => {
//       this.log.debug("OK on insertMany:", result)
//    }).catch(err => {
//       this.log.error("Writing agents", err)
//    })
    
//    this.agents = res.rows
//    if (!this.agent && this.agents.length > 0) this.agent = 0
//    this.mdb.connect
  }
  
  eatParms(err, res) {						//Digest operating parameters from database
    if (err) {this.log.error('In query:', err.stack); return}
    res.rows.forEach((row) => {
      let { parm, value } = row
      this.parms[parm] = value
    })

    if (this.intervalTimer) clearInterval(this.intervalTimer)	//Restart interval timer
    this.intervalTimer = setInterval(()=>{
      if (this.agent != null) this.process()
    }, this.parms.interval)
  }
  
  close() {							//Shut down this controller
    this.log.debug("Shutting down agent handler")
    if (this.sqlDB.client.activeQuery) {				//If there is a query in process
      setTimeout(this.close, 500)				//Try again in a half second
    } else {
      this.sqlDB.disconnect()
    }
    if (this.intervalTimer) clearInterval(this.intervalTimer)
  }

  process() {							//Iterate on a single agent
    let aData = this.agents[this.agent]
      , actSpace = Math.random()
    this.log.debug("Running agent handler", this.agent, "of", this.agents.length)
    this.log.debug("  Person:", aData.id, aData.std_name)

    if (aData.stocks <= 0 || actSpace < this.parms.addclient) {				//I don't have any clients (or a job)
      let clients = this.agents.slice(0).sort((a,b)=>{return a.foils - b.foils})	//Sort potential clients by how many vendors they have
        , clIdx = Math.floor(Math.random() * clients.length / 4)			//Look in the first 25% of sort
        , cData
      for(cData = clients[clIdx]; clIdx < clients.length; cData = clients[clIdx++])
        if (aData.id != cData.id && !aData.partners.includes(cData.id)) break		//Don't link to myself or the same person twice
      this.log.debug("  attempt to ask:", cData.std_name, "to be my client", aData.stocks, cData.foils, clIdx)
      if (clIdx < clients.length && aData.stocks < 2 && cData.foils < 4)
        this.createTally(aData, cData)

    } else if (aData.foils <= 0 || actSpace < this.parms.addvendor) {			//I don't have any vendors, places to buy things
      let vendors = this.agents.slice(0).sort((a,b)=>{return a.stocks - b.stocks})	//Sort potential vendors by how many vendors they have
        , vdIdx = Math.floor(Math.random() * vendors.length / 4)			//Look in the first 25% of sort
        , vData
      for(vData = vendors[vdIdx]; vdIdx < vendors.length; vData = vendors[vdIdx++])
        if (aData.id != vData.id && !aData.partners.includes(vData.id)) break		//Don't link to myself or the same person twice
      this.log.debug("  attempt to ask:", vData.std_name, "to be my vendor", vData.stocks, aData.foils, vdIdx)
      if (vdIdx < vendors.length && vData.stocks < 2 && aData.foils < 4)
        this.createTally(vData, aData)

    } else if (aData.foils > 0) {
      let vIdx = Math.floor(Math.random() * aData.foils)
        , vId = aData.vendors[vIdx]
        , vData = vId ? this.agents.find(el=>(el.id == vId)) : null
      this.log.debug("  actSpace:", actSpace, "; Pay a vendor", vIdx, 'of', aData.vendors.length, vId)
      if (vData) this.payVendor(aData, vData)
    }

    if (++this.agent >= this.agents.length) this.agent = 0	//Go to next agent next time
  }

  createTally(vData, cData) {					//We are not asking--just forcing (which would normally be illegal) an open tally into the DB
    let guidNS = uuidv5(vData.peer_cdi, uuidv5.DNS)
      , guid = uuidv5(cData.peer_cdi, guidNS)
      , sig = "Valid"
      , sql = `insert into mychips.tallies (tally_ent,partner,tally_guid,tally_type,status,user_sig,part_sig) values 
          ($1,$2,$3,'stock','open',$4,$5),
          ($6,$7,$8,'foil' ,'open',$9,$10) returning tally_seq;`
    this.sqlDB.query(sql, [vData.id,cData.id,guid,sig,sig,cData.id,vData.id,guid,sig,sig], (err,res) => {
      if (err) {this.log.error('In query:', err.stack); return}
      this.log.debug("  init tally vendor:", vData.std_name, "; client:", cData.std_name)
      vData.stocks++
      cData.foils++
    })
  }

  payVendor(aData, vData) {
    let guidNS = uuidv5(vData.peer_cdi, uuidv5.DNS)
      , guid = uuidv5(aData.peer_cdi, guidNS)
      , sig = "Valid"
      , units = Math.floor(Math.random() * 100000)
      , sql = `insert into mychips.chits (chit_ent,chit_seq,chit_guid,chit_type,signature,units) values 
          ($1,mychips.tally_find($1,$5,'foil'),$2,'tran',$3,$4),
          ($5,mychips.tally_find($5,$1,'stock'),$6,'tran',$7,$8) returning chit_seq;`
    this.log.debug("  payment:", aData.id, vData.id)
    this.sqlDB.query(sql, [aData.id,guid,sig,units,vData.id,guid,sig,units], (err,res) => {
      if (err) {this.log.error('In query:', err.stack); return}
      this.log.debug("  payment:", aData.id, aData.std_name, "to:", vData.id, vData.std_name)
    })
  }

}		//class AgentCont

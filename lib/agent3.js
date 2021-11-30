// rxjs observables

const SQLManager = require('./agent3/sqlmanager')
const MongoManager = require('./agent3/mongomanager')
const Os = require('os')
const DocClient = require('mongodb').MongoClient
const MongoOpts = { useNewUrlParser: true, useUnifiedTopology: true }
const { Log } = require('wyclif')
const uuidv4 = require('uuid/v4')
const userFields = ['id', 'std_name', 'peer_cid', 'serv_id']
const parmQuery = "select parm,value from base.parm_v where module = 'agent'"

const userSql = `select id, std_name, ent_name, fir_name, ent_type, user_ent,
	peer_cid, peer_sock, stocks, foils, partners, vendors, clients,
	vendor_cids, client_cids, stock_seqs, foil_seqs, units, types, seqs, targets
	from mychips.users_v_tallysum
	where not peer_ent isnull`
const peerSql = `insert into mychips.peers_v 
	(ent_name, fir_name, ent_type, born_date, peer_cid, peer_host, peer_port) 
	values ($1, $2, $3, $4, $5, $6, $7) returning *`

module.exports = class AgentCluster {
  #params
  #sqlManager
  #mongoManager
  #logger

  constructor(sqlConfig, mongoConfig, argv) {
    this.loadParamsConfig()
    this.configureDatabases(sqlConfig, mongoConfig, argv)
    this.run()
  }

  configureDatabases(sqlConfig, mongoConfig, argv) {
    // Initialize agent logger
    this.#logger = Log('agent')

    // Configure SQLManager
    this.#sqlManager = new SQLManager(sqlConfig, this.#logger, this.#params)
    this.#mongoManager = new MongoManager(mongoConfig)
  }

  // calls run on all of the agents
  run() {
    this.agents = []

    this.remoteIdx = 0 //Use to make unique tag for each remote command
    this.remoteCBs = {} //Store routines to call on completion

    this.agent = null //Keep track of which user we are processing
    this.counter = 0
    if (argv.runs) {
      this.runs = argv.runs
    } //Max iterations
    this.#sqlManager.createConnection(
      this.#params,
      this.eatAgents,
      this.notifyOfParamsChange,
      this.notifyOfTallyChange
    )

    this.intervalTimer = null
    this.#sqlManager.query(parmQuery, (e, r) => {
      this.eatParms(e, r)
    }) //Load initial parameters

    //    this.worldPop = 40					//Init to any reasonable value

    this.#mongoManager.createConnection(MongoOpts, this.loadInitialUsers)
  }

  loadInitialUsers() {
    this.#sqlManager.query(userSql, (e, r) => {
      this.eatAgents(e, r, true)
    }) //Load up initial set of users
  }

  // gets the params from the SQLManager
  eatParams() {}

  // gets agents from SQL and puts hosted agent info into MongoDB
  notifyEatAgents() {}

  notifyOfParamsChange(target, value) {
    this.#params[target] = value
  }

  notifyOfTallyChange(msg) {
    this.tallyState(msg)
  }

  notifyOfAction() {}

  loadParamsConfig() {
    const fs = require('fs')
    const yaml = require('js-yaml')

    try {
      let fileContents = fs.readFileSync('./agent3/paramConfig.yaml', 'utf8')
      this.#params = yaml.load(fileContents)

      console.log(this.#params)
    } catch (e) {
      console.log(e)
    }
  }

  // -----------------------------------------------------------------------------
  remoteCall(host, cmd, data, cb) {
    //Execute command on foreign peer
    let tag = host + '.' + this.remoteIdx++ //Make unique message ID
    this.log.debug('Remote calling:', cmd, 'to:', host)
    this.remoteCBs[tag] = cb //Remember what to call locally on completion
    this.docAc.insertOne(
      { action: cmd, tag, host, from: this.host, data },
      null,
      (err, res) => {
        if (err) this.log.error('Sending remote command:', cmd, 'to:', host)
      }
    )
  }

  // -----------------------------------------------------------------------------
  eatAgents(err, res, all) {
    //Freshly load agent data from database
    if (err) {
      this.log.error('In query:', err.stack)
      return
    }
    if (!this.docDB) return //Document db connected/ready
    this.log.trace('Loaded agents:', res.rows.length)
    let haveEm = [] //Keep track of which ones we've processed

    res.rows.forEach((row) => {
      //For each agent in sql
      let aIdx = this.agents.findIndex((el) => el.peer_cid == row.peer_cid)
      if (aIdx >= 0) this.agents[aIdx] = row
      else this.agents.push(row) //Keep local copy
      if (row.user_ent) {
        //If this is one we host, update world db
        haveEm.push(row.peer_cid)
        row.random = Math.random()
        row.host = this.host //Mark user as belonging to us
        this.docAg.updateOne(
          { peer_cid: row.peer_cid, host: row.host },
          { $set: row },
          { upsert: true },
          (e, r) => {
            if (e) this.log.error(e.message)
            else this.log.trace('Add/update agent:', r)
          }
        )
      }
    })

    if (all)
      this.docAg.deleteMany(
        {
          //Delete any strays left in world db
          host: this.host,
          peer_cid: { $nin: haveEm },
        },
        (e, r) => {
          if (e) this.log.error(e.message)
          else this.log.debug('Delete agents in world:', r.n)
        }
      )

    if (!this.agent && this.agents.length > 0) this.agent = 0 //Initialize loop to traverse agents
  }

  // -----------------------------------------------------------------------------
  eatParms(err, res) {
    //Digest operating parameters from database
    this.log.trace('eatParms')
    if (err) {
      this.log.error('In query:', err.stack)
      return
    }
    res.rows.forEach((row) => {
      let { parm, value } = row
      this.#params[parm] = value
    })

    if (this.intervalTimer) clearInterval(this.intervalTimer) //Restart interval timer
    this.intervalTimer = setInterval(() => {
      if (this.agent != null && (!this.runs || this.counter < this.runs))
        this.process(++this.counter)
    }, this.#params.interval)
  }

  // -----------------------------------------------------------------------------
  close() {
    //Shut down this controller
    this.log.debug('Shutting down agent handler')
    if (this.sqlDB.client.activeQuery) {
      //If there is a query in process
      setTimeout(this.close, 500) //Try again in a half second
    } else {
      this.sqlDB.disconnect()
    }
    if (this.intervalTimer) clearInterval(this.intervalTimer)
  }

  // -----------------------------------------------------------------------------
  process(run) {
    //Iterate on a single agent
    let aData = this.agents[this.agent], //Point to agent's data
      actSpace = Math.random(), //Randomize what action we will take
      startAgent = this.agent
    while (!aData.user_ent) {
      if (++this.agent >= this.agents.length) this.agent = 0
      this.log.trace('  Skipping non-local partner:', this.agent, startAgent)
      if (this.agent == startAgent) return //Avoid infinite loop if no users found
      aData = this.agents[this.agent]
    }
    this.log.verbose(
      'Handler',
      run,
      this.agent,
      'of',
      this.agents.length,
      aData.id,
      aData.std_name,
      aData.peer_cid
    )
    if (++this.agent >= this.agents.length) this.agent = 0 //Will go to next agent next time

    this.log.debug(
      '  stocks:',
      aData.stocks,
      this.#params.maxstocks,
      '  foils:',
      this.#params.maxfoils,
      'space:',
      actSpace
    )
    if (
      aData.stocks <= 0 ||
      (actSpace < this.#params.addclient &&
        aData.stocks < this.#params.maxstocks)
    ) {
      //I don't have any, or enough clients (or jobs)
      this.docAg.findOneAndUpdate(
        {
          //Look for a trading partner
          peer_cid: {
            $ne: aData.peer_cid, //Don't find myself
            $nin: aData.partners, //Or anyone I'm already connected to
          },
          //        host: {$ne: this.host},			//Look only on other hosts
          foils: { $lte: this.#params.maxfoils }, //Or those with not too many foils already
        },
        {
          $set: { random: Math.random() }, //re-randomize this person
          $inc: { foils: 1 }, //And make it harder to get them again next time
          $push: { partners: aData.peer_cid }, //Immediately add ourselves to the array to avoid double connecting
        },
        {
          //Sort by
          sort: { foils: 1, random: -1 },
        },
        (e, res) => {
          //Get result of query
          if (e) {
            this.log.error(e.errmsg)
          } else if (res.ok) {
            this.log.verbose(
              '  Best client:',
              res.value.std_name,
              res.value.host
            )
            this.tryTally(aData, res.value)
          } else {
            this.log.verbose('  No client found in world DB')
          }
        }
      ) //findOneAndUpdate
    } else if (
      actSpace < this.#params.checksets &&
      aData.targets.some((el, ix) => {
        return !parseInt(el) && aData.types[ix] == 'foil'
      })
    ) {
      //Could do something more interesting with channel settings
      this.log.debug('  Set targets:', aData.targets)
      this.chkSettings(aData)

      //    } else if (aData.foils <= 0 || actSpace < this.#params.addvendor) {			//I don't have any vendors, places to buy things
      //      let vendors = this.agents.slice(0).sort((a,b)=>{return a.stocks - b.stocks})	//Sort potential vendors by how many vendors they have
      //        , vdIdx = Math.floor(Math.random() * vendors.length / 4)			//Look in the first 25% of sort
      //        , vData
      //      for(vData = vendors[vdIdx]; vdIdx < vendors.length; vData = vendors[vdIdx++])
      //        if (aData.id != vData.id && !aData.partners.includes(vData.id)) break		//Don't link to myself or the same person twice
      //      this.log.debug("  attempt to ask:", vData.std_name, "to be my vendor", vData.stocks, aData.foils, vdIdx)
      //      if (vdIdx < vendors.length && vData.stocks < 2 && aData.foils < 4)
      //        this.createTally(vData, aData)
      //
    } else if (aData.foils > 0 && aData.units > this.#params.mintotpay) {
      let vIdx = Math.floor(Math.random() * aData.foils),
        vId = aData.vendors[vIdx],
        vData = vId ? this.agents.find((el) => el.id == vId) : null
      this.log.debug(
        '  I:',
        aData.id,
        '; Pay a vendor',
        vIdx,
        'of',
        aData.vendors.length,
        vId,
        'NW:',
        aData.units
      )
      if (vData) this.payVendor(aData, vIdx, vData)
    }
  }

  // -----------------------------------------------------------------------------
  tryTally(aData, pDoc) {
    //Try to request tally from someone in the world
    this.log.debug('  Try tally:', aData.peer_cid, 'with', pDoc.peer_cid)
    this.checkPeer(pDoc, (pData, hadEm) => {
      let host = pDoc.peer_sock.split(':')[0]

      this.remoteCall(host, 'createUser', aData, () => {
        //Insert this peer remotely
        let guid = uuidv4(),
          sig = 'Valid',
          contract = { name: 'mychips-0.99' },
          tallySql =
            'insert into mychips.tallies_v (tally_ent, tally_guid, partner, user_sig, contract, request) values ($1, $2, $3, $4, $5, $6);',
          partner = 'test'

        this.log.debug('Tally request:', tallySql, aData.id, pData.id)
        this.sqlDB.query(
          tallySql,
          [aData.id, guid, pData.id, sig, contract, 'draft'],
          (err, res) => {
            if (err) {
              this.log.error('In query:', err.stack)
              return
            }
            this.log.debug(
              '  Initial tally by:',
              aData.std_name,
              ' with partner:',
              pData.std_name
            )
            aData.stocks++
            //          pData.foils++
          }
        )
      })
    })
  }

  // Check to see if a peer is in our system, if not add them and then do cb
  // -----------------------------------------------------------------------------
  checkPeer(pData, cb) {
    //Make sure we have a peer in our system
    let host,
      port,
      aData = this.agents.find((el) => el.peer_cid == pData.peer_cid)
    if (pData.peer_sock) {
      ;[host, port] = pData.peer_sock.split(':')
    } //If default socket, use it for host,port

    this.log.debug('Checking if we have peer:', pData.peer_cid, !!aData)
    if (aData) cb(aData, true)
    else if (pData.host == this.host)
      this.log.error('Should have had local user:', pData.peer_cid)
    else
      this.sqlDB.query(
        peerSql,
        [
          pData.ent_name,
          pData.fir_name,
          pData.ent_type,
          pData.born_date,
          pData.peer_cid,
          pData.peer_host || host,
          pData.peer_port || port,
        ],
        (err, res) => {
          if (err) {
            this.log.error('Adding peer:', pData.peer_cid, err.stack)
            return
          }
          let newGuy = res.rows[0]
          this.log.debug(
            '  Inserting partner locally:',
            newGuy.std_name,
            newGuy.peer_sock
          )
          this.agents.push(newGuy)
          cb(newGuy)
        }
      )
  }

  // -----------------------------------------------------------------------------
  tallyState(msg) {
    //Someone is asking an agent to act on a tally
    this.log.debug('Peer Message:', msg)

    if (msg.state == 'peerProffer') {
      //For now, we will just answer 'yes'
      this.log.verbose('  peerProffer:', msg.entity)
      this.sqlDB.query(
        "update mychips.tallies_v set request = 'open' where tally_ent = $1 and tally_seq = $2",
        [msg.entity, msg.sequence],
        (e, r) => {
          if (e) {
            this.log.error('In :', e.stack)
            return
          }
          //        let row = r.rows && r.rows.length >= 1 ? r.rows[0] : null
          //          , aData = this.agents.findIndex(el=>(el.peer_cid == row.peer_cid))
          this.log.verbose('  Tally affirmed:', msg.object)
        }
      )
    }
  }

  // -----------------------------------------------------------------------------
  payVendor(aData, vIdx, vData) {
    let guid = uuidv4(),
      sig = 'Valid',
      max = Math.max(aData.units * this.#params.maxtopay, 1000), //Pay 1 CHIP or % of net worth
      units = Math.floor(Math.random() * max),
      seq = aData.foil_seqs[vIdx], //Tally sequence
      quid = 'Inv' + Math.floor(Math.random() * 1000),
      req = 'userDraft',
      sql =
        "insert into mychips.chits_v (chit_ent,chit_seq,chit_guid,chit_type,signature,units,quidpro,request) values ($1,$2,$3,'tran',$4,$5,$6,$7)"

    this.log.verbose(
      '  payVendor:',
      aData.id,
      '->',
      vData.id,
      'on:',
      seq,
      'Units:',
      units
    )
    this.sqlDB.query(
      sql,
      [aData.id, seq, guid, sig, units, quid, req],
      (e, r) => {
        if (e) {
          this.log.error('In payment:', e.stack)
          return
        }
        this.log.debug(
          '  payment:',
          aData.id,
          aData.std_name,
          'to:',
          vData.id,
          vData.std_name
        )
      }
    )
  }

  // -----------------------------------------------------------------------------
  chkSettings(aData) {
    let sqls = [],
      i = 0

    aData.targets.forEach((t) => {
      let seq = aData.seqs[i],
        ent = aData.id,
        newTarg = parseInt(Math.random() * this.#params.maxtarget),
        newBound = parseInt(Math.random() * newTarg * 0.5) + newTarg,
        reward = parseInt(Math.random() * 5) / 100 + 0.05
      this.log.trace('   seq:', seq, 'type:', aData.types[i])
      if (aData.types[i] == 'foil') {
        //For now, we will assert settings only on foil tallies
        sqls.push(
          `insert into mychips.tally_sets (tset_ent, tset_seq, target, bound, reward, signature) values ('${ent}', ${seq}, ${newTarg}, ${newBound}, ${reward}, 'Valid')`
        )
      }
      i++
    })
    this.log.debug('  Settings:', sqls.join(';'))
    this.sqlDB.query(sqls.join(';'), null, (e, r) => {
      if (e) {
        this.log.error('In settings:', e.stack)
        return
      }
    })
  }
}

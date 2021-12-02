// rxjs observables

const SQLManager = require('./agent3/sqlmanager')
const MongoManager = require('./agent3/mongomanager')
const Os = require('os')
const DocClient = require('mongodb').MongoClient
const WorldDBOpts = { useNewUrlParser: true, useUnifiedTopology: true }
const { Log } = require('wyclif')
const uuidv4 = require('uuid/v4')
const userFields = ['id', 'std_name', 'peer_cid', 'serv_id']
const parmQuery = "select parm,value from base.parm_v where module = 'agent'"


module.exports = class AgentCluster {
  #argv
  #host
  #params
  #myChipsDBManager
  #worldDBManager
  #logger

  #counter
  #intervalTimer
  #runs

  #currAgent
  #agents
  #remoteIdx //Use to make unique tag for each remote command
  #remoteCBs //Store routines to call on completion

  constructor(myChipsDBConfig, worldDBConfig, argv) {
    this.#argv = argv
    this.#host = argv.peerServer || Os.hostname()

    // Bind functions we are passing as callbacks (makes sure `this` always refers to this object)
    this.loadInitialUsers = this.loadInitialUsers.bind(this)
    this.notifyTryTally = this.notifyTryTally.bind(this)
    this.notifyOfTallyChange = this.notifyOfTallyChange.bind(this)
    this.checkPeer = this.checkPeer.bind(this)
    this.notifyOfActionDone = this.notifyOfActionDone.bind(this)
    this.notifyOfAgentsChange = this.notifyOfAgentsChange.bind(this)

    // Initialize agent logger
    this.#logger = Log('agent')
    this.#logger.info('Initializing agent model controller 3 on:', this.#host)
    this.loadParamsConfig()
    this.configureDatabases(myChipsDBConfig, worldDBConfig)
    this.run()
  }

  configureDatabases(myChipsDBConfig, worldDBConfig) {
    // Configure SQLManager
    this.#myChipsDBManager = new SQLManager(myChipsDBConfig, this.#logger, this.#params)
    // Configure MongoManager
    this.#worldDBManager = new MongoManager(worldDBConfig, this.#logger, this.#argv)
  }

  // calls run on all of the agents
  run() {
    this.#agents = []

    this.#remoteIdx = 0 //Use to make unique tag for each remote command
    this.#remoteCBs = {} //Store routines to call on completion

    this.#currAgent = null //Keep track of which user we are processing
    this.#counter = 0
    if (this.#argv.runs) {
      this.#runs = this.#argv.runs
    } //Max iterations
    this.#myChipsDBManager.createConnection(
      this.#params,
      this.notifyOfAgentsChange,
      this.notifyOfParamsChange,
      this.notifyOfTallyChange
    )

    this.#intervalTimer = null
    // TODO: determine if this is necessary with new paramConfig.yaml
    this.#myChipsDBManager.query(parmQuery, (e, r) => {
      this.eatParams(e, r)
    }) //Load initial parameters

    //    this.worldPop = 40					//Init to any reasonable value

    this.#worldDBManager.createConnection(WorldDBOpts, this.checkPeer, this.notifyOfActionDone, this.loadInitialUsers)

    // TODO: Add Agent stuff here (something like this...)
    // for (var i = 0; i < #runs; i++) {
    //   this.#agents.forEach(agent => {
    //     agent.process()
    //   })
    // }
  }

  // Loads parameters from the config file
  loadParamsConfig() {
    const fs = require('fs')
    const yaml = require('js-yaml')

    try {
      let fileContents = fs.readFileSync(__dirname + '/agent3/paramConfig.yaml')
      this.#params = yaml.load(fileContents)

      console.log(this.#params)
      // TODO: Build agents using the AgentFactory
    } catch (e) {
      console.log(e)
      this.#logger.error(e)
    }
  }

  // --- Functions passed as callbacks -------------------------------------------------------
  // Loads agents from the MyCHIPs Database
  loadInitialUsers() {
    this.#myChipsDBManager.queryUsers((e, r) => {
      this.eatAgents(e, r, true)
    }) //Load up initial set of users
  }

  // gets agents from SQL and puts hosted agent info into MongoDB
  notifyOfAgentsChange(msg) {
    this.#myChipsDBManager.queryLatestUsers(msg.time, (e, r) => {
      this.eatAgents(e, r)
    })
  }

  notifyOfParamsChange(target, value) {
    this.#params[target] = value
  }

  notifyOfTallyChange(msg) {
    this.tallyState(msg)
  }

  notifyTryTally(aData, queryResponseVal) {
    this.tryTally(aData, queryResponseVal)
  }

  // TODO: Decouple from Mongo
  notifyOfActionDone(doc) {
    //Remote action has completed
    this.#logger.debug('Remote call done:', doc.tag, 'from:', doc.from)
    if (this.#remoteCBs[doc.tag]) {
      //If I can find a stored callback
      this.#remoteCBs[doc.tag]() //Call it
      delete this.#remoteCBs[doc.tag] //And then forget about it
    }
  }

  notifyOfAction() {}

  // Check to see if a peer is in our system, if not add them and then do cb
  // TODO: fix up variable naming
  checkPeer(pData, cb) {
    //Make sure we have a peer in our system
    let host,
      port,
      aData = this.#agents.find((el) => el.peer_cid == pData.peer_cid)
    if (pData.peer_sock) {
      ;[host, port] = pData.peer_sock.split(':')
    } //If default socket, use it for host,port

    this.#logger.debug('Checking if we have peer:', pData.peer_cid, !!aData)
    if (aData) cb(aData, true)
    else if (pData.host == this.host)
      this.#logger.error('Should have had local user:', pData.peer_cid)
    else
      this.#myChipsDBManager.query(
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
            this.#logger.error('Adding peer:', pData.peer_cid, err.stack)
            return
          }
          let newGuy = res.rows[0]
          this.#logger.debug(
            '  Inserting partner locally:',
            newGuy.std_name,
            newGuy.peer_sock
          )
          this.#agents.push(newGuy)
          cb(newGuy)
        }
      )
  }

  // -----------------------------------------------------------------------------

  // --- Helper Functions --------------------------------------------------------
  // Executes a command on a foreign peer
  remoteCall(host, cmd, data, cb) {
    let tag = host + '.' + this.#remoteIdx++ //Make unique message ID
    this.#logger.debug('Remote calling:', cmd, 'to:', host)
    this.#remoteCBs[tag] = cb //Remember what to call locally on completion
    this.#worldDBManager.insertAction(cmd, tag, host, data)
  }

  // gets the agents from the SQLManager
  eatAgents(err, res, all) {
    //Freshly load agent data from database
    if (err) {
      this.#logger.error('In query:', err.stack)
      return
    }
    if (!this.#worldDBManager.isDBClientConnected()) return //Document db connected/ready
    this.#logger.trace('Loaded agents:', res.rows.length)
    let haveEm = [] //Keep track of which ones we've processed

    res.rows.forEach((row) => {
      //For each agent in sql
      let aIdx = this.#agents.findIndex((el) => el.peer_cid == row.peer_cid)
      if (aIdx >= 0) this.#agents[aIdx] = row
      else this.#agents.push(row) //Keep local copy
      if (row.user_ent) {
        //If this is one we host, update world db
        haveEm.push(row.peer_cid)
        row.random = Math.random()

        this.#worldDBManager.updateOneAgent(row)
      }
    })

    if (all) this.#worldDBManager.deleteManyAgents(haveEm)

    if (!this.#currAgent && this.#agents.length > 0) this.#currAgent = 0 //Initialize loop to traverse agents
  }

  // -----------------------------------------------------------------------------
  eatParams(err, res) {
    //Digest operating parameters from database
    this.#logger.trace('eatParams')
    if (err) {
      this.#logger.error('In query:', err.stack)
      return
    }
    res.rows.forEach((row) => {
      let { param, value } = row
      this.#params[param] = value
    })

    if (this.#intervalTimer) clearInterval(this.#intervalTimer) //Restart interval timer
    this.#intervalTimer = setInterval(() => {
      if (
        this.#currAgent != null &&
        (!this.#runs || this.#counter < this.#runs)
      )
        this.process(++this.#counter)
    }, this.#params.interval)
  }

  // -----------------------------------------------------------------------------
  close() {
    //Shut down this controller
    this.#logger.debug('Shutting down agent handler')
    if (this.#myChipsDBManager.isActiveQuery()) {
      //If there is a query in process
      setTimeout(this.close, 500) //Try again in a half second
    } else {
      this.#myChipsDBManager.closeConnection()
    }
    if (this.#intervalTimer) clearInterval(this.#intervalTimer)
  }

  // -----------------------------------------------------------------------------
  // TODO: move this over to the Agent code
  process(run) {
    //Iterate on a single agent
    let aData = this.#agents[this.#currAgent], //Point to agent's data
      actSpace = Math.random(), //Randomize what action we will take
      startAgent = this.#currAgent
    while (!aData.user_ent) {
      if (++this.#currAgent >= this.#agents.length) this.#currAgent = 0
      this.#logger.trace(
        '  Skipping non-local partner:',
        this.#currAgent,
        startAgent
      )
      if (this.#currAgent == startAgent) return //Avoid infinite loop if no users found
      aData = this.#agents[this.#currAgent]
    }
    this.#logger.verbose(
      'Handler',
      run,
      this.#currAgent,
      'of',
      this.#agents.length,
      aData.id,
      aData.std_name,
      aData.peer_cid
    )
    if (++this.#currAgent >= this.#agents.length) this.#currAgent = 0 //Will go to next agent next time

    this.#logger.debug(
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
      this.#worldDBManager.findOneAndUpdate(
        aData,
        this.#params.maxfoils,
        this.notifyTryTally
      )
    } else if (
      actSpace < this.#params.checksets &&
      aData.targets.some((el, ix) => {
        return !parseInt(el) && aData.types[ix] == 'foil'
      })
    ) {
      //Could do something more interesting with channel settings
      this.#logger.debug('  Set targets:', aData.targets)
      this.chkSettings(aData)

      //    } else if (aData.foils <= 0 || actSpace < this.#params.addvendor) {			//I don't have any vendors, places to buy things
      //      let vendors = this.#agents.slice(0).sort((a,b)=>{return a.stocks - b.stocks})	//Sort potential vendors by how many vendors they have
      //        , vdIdx = Math.floor(Math.random() * vendors.length / 4)			//Look in the first 25% of sort
      //        , vData
      //      for(vData = vendors[vdIdx]; vdIdx < vendors.length; vData = vendors[vdIdx++])
      //        if (aData.id != vData.id && !aData.partners.includes(vData.id)) break		//Don't link to myself or the same person twice
      //      this.#logger.debug("  attempt to ask:", vData.std_name, "to be my vendor", vData.stocks, aData.foils, vdIdx)
      //      if (vdIdx < vendors.length && vData.stocks < 2 && aData.foils < 4)
      //        this.createTally(vData, aData)
      //
    } else if (aData.foils > 0 && aData.units > this.#params.mintotpay) {
      let vIdx = Math.floor(Math.random() * aData.foils),
        vId = aData.vendors[vIdx],
        vData = vId ? this.#agents.find((el) => el.id == vId) : null
      this.#logger.debug(
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

  // TODO: --- Functions that need to be moved to Actions ---------------------------------------
  tryTally(aData, pDoc) {
    //Try to request tally from someone in the world
    this.#logger.debug('  Try tally:', aData.peer_cid, 'with', pDoc.peer_cid)
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

        this.#logger.debug('Tally request:', tallySql, aData.id, pData.id)

        this.#myChipsDBManager.query(
          tallySql,
          [aData.id, guid, pData.id, sig, contract, 'draft'],
          (err, res) => {
            if (err) {
              this.#logger.error('In query:', err.stack)
              return
            }
            this.#logger.debug(
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

  // -----------------------------------------------------------------------------
  tallyState(msg) {
    //Someone is asking an agent to act on a tally
    this.#logger.debug('Peer Message:', msg)

    if (msg.state == 'peerProffer') {
      //For now, we will just answer 'yes'
      this.#logger.verbose('  peerProffer:', msg.entity)
      this.#myChipsDBManager.query(
        "update mychips.tallies_v set request = 'open' where tally_ent = $1 and tally_seq = $2",
        [msg.entity, msg.sequence],
        (e, r) => {
          if (e) {
            this.#logger.error('In :', e.stack)
            return
          }
          //        let row = r.rows && r.rows.length >= 1 ? r.rows[0] : null
          //          , aData = this.#agents.findIndex(el=>(el.peer_cid == row.peer_cid))
          this.#logger.verbose('  Tally affirmed:', msg.object)
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

    this.#logger.verbose(
      '  payVendor:',
      aData.id,
      '->',
      vData.id,
      'on:',
      seq,
      'Units:',
      units
    )
    this.#myChipsDBManager.query(
      sql,
      [aData.id, seq, guid, sig, units, quid, req],
      (e, r) => {
        if (e) {
          this.#logger.error('In payment:', e.stack)
          return
        }
        this.#logger.debug(
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

  // TODO: Determine if this function is needed with new paramConfig.yaml -----------------------
  chkSettings(aData) {
    let sqls = [],
      i = 0

    aData.targets.forEach((t) => {
      let seq = aData.seqs[i],
        ent = aData.id,
        newTarg = parseInt(Math.random() * this.#params.maxtarget),
        newBound = parseInt(Math.random() * newTarg * 0.5) + newTarg,
        reward = parseInt(Math.random() * 5) / 100 + 0.05
      this.#logger.trace('   seq:', seq, 'type:', aData.types[i])
      if (aData.types[i] == 'foil') {
        //For now, we will assert settings only on foil tallies
        sqls.push(
          `insert into mychips.tally_sets (tset_ent, tset_seq, target, bound, reward, signature) values ('${ent}', ${seq}, ${newTarg}, ${newBound}, ${reward}, 'Valid')`
        )
      }
      i++
    })
    this.#logger.debug('  Settings:', sqls.join(';'))
    this.#myChipsDBManager.query(sqls.join(';'), null, (e, r) => {
      if (e) {
        this.#logger.error('In settings:', e.stack)
        return
      }
    })
  }
}

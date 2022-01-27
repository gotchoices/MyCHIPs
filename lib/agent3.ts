import SQLManager from './agent3/sqlmanager'
import MongoManager from './agent3/mongomanager'
import Os from 'os'
import UnifiedLogger from './agent3/unifiedLogger'
import { ActionDoc } from './@types/document'
import Agent from './agent3/agent'
import AgentFactory from './agent3/agentFactory'

const WorldDBOpts = { useNewUrlParser: true, useUnifiedTopology: true }

const userFields = ['id', 'std_name', 'peer_cid', 'serv_id']
const parmQuery = "select parm,value from base.parm_v where module = 'agent'"
const peerSql = `insert into mychips.peers_v
	(ent_name, fir_name, ent_type, born_date, peer_cid, peer_host, peer_port)
	values ($1, $2, $3, $4, $5, $6, $7) returning *`

interface AgentClusterType {
  checkPeer: CheckPeerFn
}

class AgentCluster implements AgentClusterType {
  private networkConfig: NetworkConfig
  private host: string

  /** Contains the adjustable values of the simulation */
  private params!: AdjustableSimParams
  private myChipsDBManager!: SQLManager
  private worldDBManager!: MongoManager
  private logger: WyclifLogger

  /** Number of runs the sim is set to complete */
  private runs!: number
  /** Counts number of runs the simulation executes / tracks current run */
  private runCounter!: number
  // TODO: Not sure what this does
  private intervalTimer!: NodeJS.Timer | null

  private allKnownAgents!: AgentData[]
  private hostedAgents!: Agent[]

  /** Use to make unique tag for each remote command */
  private remoteIdx!: number
  private remoteCBs!: { [x: string]: any } //Store routines to call on completion

  constructor(
    myChipsDBConfig: DBConfig,
    worldDBConfig: DBConfig,
    networkConfig: NetworkConfig
  ) {
    this.networkConfig = networkConfig
    this.host = networkConfig.peerServer || Os.hostname()

    // Bind functions we are passing as callbacks (makes sure `this` always refers to this object)
    this.loadInitialUsers = this.loadInitialUsers.bind(this)
    this.notifyTryTally = this.notifyTryTally.bind(this)
    this.notifyOfTallyChange = this.notifyOfTallyChange.bind(this)
    this.checkPeer = this.checkPeer.bind(this)
    this.notifyOfActionDone = this.notifyOfActionDone.bind(this)
    this.notifyOfAgentsChange = this.notifyOfAgentsChange.bind(this)

    // Initialize agent logger
    this.logger = UnifiedLogger.getInstance()
    this.logger.info('Initializing agent model controller 3 on:', this.host)
    this.loadParamsConfig()
    this.configureDatabases(myChipsDBConfig, worldDBConfig)
    this.run()
  }
  
  // Loads parameters from the config file
  loadParamsConfig() {
    const fs = require('fs')
    const yaml = require('js-yaml')

    try {
      let fileContents = fs.readFileSync(__dirname + '/agent3/paramConfig.yaml')
      this.params = yaml.load(fileContents)
      console.log(this.params)
    } catch (e) {
      console.log(e)
      this.logger.error(e)
    }
  }

  configureDatabases(myChipsDBConfig: DBConfig, worldDBConfig: DBConfig) {
    // Configure SQLManager
    this.myChipsDBManager = SQLManager.getInstance(
      myChipsDBConfig,
      this.params
    )
    // Configure MongoManager
    this.worldDBManager = MongoManager.getInstance(
      worldDBConfig,
      this.networkConfig
    )
  }

  // calls run on all of the agents
  run() {
    console.log('RUNNING AGENT MODEL * VERSION 3 *')
    this.logger.info('RUNNING AGENT MODEL V3')

    this.allKnownAgents = []
    this.remoteIdx = 0 //Use to make unique tag for each remote command
    this.remoteCBs = {} //Store routines to call on completion

    this.runCounter = 0
    if (this.networkConfig.runs) {
      this.runs = this.networkConfig.runs
    } //Max iterations

    this.myChipsDBManager.createConnection(
      this.notifyOfAgentsChange,
      this.notifyOfParamsChange,
      this.notifyOfTallyChange
    )

    this.intervalTimer = null
    // TODO: determine if this is necessary with new paramConfig.yaml
    this.myChipsDBManager.query(parmQuery, (e, r) => {
      this.eatParams(e, r)
    }) //Load initial parameters

    //    this.worldPop = 40					//Init to any reasonable value

    this.worldDBManager.createConnection(
      WorldDBOpts,
      this.checkPeer,
      this.notifyOfActionDone,
      // loadInitialUsers is called once the connection is created asynchronously
      this.loadInitialUsers
    )

  }

  // Replaces checkPeer() in agent2
  ensurePeerInSystem() {}

  // --- Functions passed as callbacks -------------------------------------------------------
  // Loads agents from the MyCHIPs Database
  loadInitialUsers() {
    this.myChipsDBManager.queryUsers(this.eatAgents) //Load up initial set of users
  }

  // gets agents from SQL and puts hosted agent info into MongoDB
  notifyOfAgentsChange(msg) {
    this.myChipsDBManager.queryLatestUsers(msg.time, this.eatAgents)
  }

  notifyOfParamsChange(target, value) {
    this.params[target] = value
  }

  notifyOfTallyChange(msg: any) {
    this.tallyState(msg)
  }

  notifyTryTally(aData: any, queryResponseVal: any) {
    this.tryTally(aData, queryResponseVal)
  }

  // TODO: Decouple from Mongo
  notifyOfActionDone(doc: ActionDoc) {
    //Remote action has completed
    this.logger.debug('Remote call done:', doc.tag, 'from:', doc.from)
    if (this.remoteCBs[doc.tag]) {
      //If I can find a stored callback
      this.remoteCBs[doc.tag!]() //Call it
      delete this.remoteCBs[doc.tag] //And then forget about it
    }
  }

  notifyOfAction() {}

  // Check to see if a peer is in our system, if not add them and then do cb
  // TODO: fix up variable naming
  checkPeer(
    peerData: AgentData,
    onFinishCreatingUser: (agentData: AgentData) => void
  ): void {
    //Exit if there are no agents in our system
    if (this.allKnownAgents == undefined) {
      this.logger.debug('There are no agents in the system')
      return
    }

    console.log('this.agents: ', this.allKnownAgents) //TODO remove this
    let host: string
    let port: string
    //Get data for the first matching peer in the system
    let agentData = this.allKnownAgents.find((agentElement) => agentElement.peer_cid == peerData.peer_cid)
    
    //Exit if no matching peer found
    if (agentData === undefined) {
      this.logger.debug('No match was found for peer ', peerData.peer_cid)
      return
    }

    //If default socket, use it for host,port
    if (peerData.peer_socket) {
      this.logger.debug('Using ', peerData.peer_socket, ' as host port')
      ;[host, port] = peerData.peer_socket.split(':')
    }

    this.logger.debug('Checking if we have peer:', peerData.peer_cid, !!agentData)
    if (agentData) { //Is this if needed since we check on line 256?
      this.logger.debug('Found match for peer', peerData.peer_cid, 'in system')
      onFinishCreatingUser(agentData)
    } 
    else if (peerData.host == this.host) {
      this.logger.error('Should have had local user:', peerData.peer_cid)
    }
    else {
      this.myChipsDBManager.query(
        peerSql,
        [
          peerData.ent_name,
          peerData.fir_name,
          peerData.ent_type,
          peerData.born_date,
          peerData.peer_cid,
          peerData.peer_host || host!,
          peerData.peer_port || port!,
        ],
        (err, res) => {
          if (err) {
            this.logger.error('Adding peer:', peerData.peer_cid, err.stack)
            return
          }
          let newGuy = res.rows[0]
          this.logger.debug(
            '  Inserting partner locally:',
            newGuy.std_name,
            newGuy.peer_socket
          )
          this.allKnownAgents.push(newGuy)
          onFinishCreatingUser(newGuy)
        }
      )
    }
  }

  // --- Helper Functions --------------------------------------------------------
  
  // -----------------------------------------------------------------------------
  // Executes a command on a foreign peer
  remoteCall(host, cmd, data, cb) {
    let tag = host + '.' + this.remoteIdx++ //Make unique message ID
    this.logger.debug('Remote calling:', cmd, 'to:', host)
    this.remoteCBs[tag] = cb //Remember what to call locally on completion
    this.worldDBManager.insertAction(cmd, tag, host, data)
  }

  // -----------------------------------------------------------------------------
  // Gets the agents from the SQLManager
  eatAgents(dbAgents: AgentData[], all?: boolean) {
    //Freshly load agent data from database
    if (!this.worldDBManager.isDBClientConnected()) {
      //Document db connected/ready
      return
    } 
    
    let processedAgents: PeerCID[] = [] //Keep track of which ones we've processed

    dbAgents.forEach((dbAgent) => {
      //For each agent in sql
      let localAgentIndex = this.allKnownAgents.findIndex((el) => el.peer_cid == dbAgent.peer_cid)
      if (localAgentIndex >= 0) {
        this.allKnownAgents[localAgentIndex] = dbAgent
      }
      else {
        this.allKnownAgents.push(dbAgent) //Keep local copy
      }
      
      if (dbAgent.user_ent) {
        //If this is one we host, update world db
        processedAgents.push(dbAgent.peer_cid)
        dbAgent.random = Math.random()

        this.worldDBManager.updateOneAgent(dbAgent)
      }
    })

    if (all) {
      this.worldDBManager.deleteManyAgents(processedAgents)
    }

    // Ensure all agents hosted on this server have an Agent object
    let localAgents = dbAgents.filter((val) => val.host == this.host)
    //TODO Add logic to determine how many of each Agent Type to create
    localAgents.forEach((agent) => {
      let hostedIndex = this.hostedAgents.findIndex((el) => el.peer_cid == agent.peer_cid)
      if (hostedIndex < 0) {
        //TODO: replace `this.params` with params specific to the agent type (from paramConfig.yaml)
        this.hostedAgents.push(AgentFactory.createAgent("BaseAgent", agent, this.params))
      }
    })
  }

  // -----------------------------------------------------------------------------
  //Digest operating parameters from database
  eatParams(err, res) {
    this.logger.trace('eatParams')
    if (err) {
      this.logger.error('In query:', err.stack)
      return
    }
    res.rows.forEach((row) => {
      let { param, value } = row
      this.params[param] = value
    })

    if (this.intervalTimer) clearInterval(this.intervalTimer) //Restart interval timer
    this.intervalTimer = setInterval(() => {
      if (!this.runs || this.runCounter < this.runs) {
        // this.process(++this.counter)
        ++this.runCounter
        this.hostedAgents.forEach(this.process)
      }
    }, this.params.interval)
  }

  // -----------------------------------------------------------------------------
  //Shut down this controller
  close() {
    this.logger.debug('Shutting down agent handler')
    if (this.myChipsDBManager.isActiveQuery()) {
      //If there is a query in process
      setTimeout(this.close, 500) //Try again in a half second
    } else {
      this.myChipsDBManager.closeConnection()
    }
    if (this.intervalTimer) clearInterval(this.intervalTimer)
  }

  // -----------------------------------------------------------------------------
  process(agent: Agent) {
    //Iterate on a single agent
    // @ts-ignore
    this.logger.verbose(
      'Handler',
      ++this.runCounter,
      agent.id,
      agent.std_name,
      agent.peer_cid
    )

    agent.takeAction()
    
    this.logger.debug(
      '  stocks:',
      agent.stocks,
      this.params.maxstocks,
      '  foils:',
      this.params.maxfoils,
      'action taken:',
      agent.lastActionTaken
    )
  }
}

export = AgentCluster

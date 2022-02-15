import SQLManager from './agent3/sqlmanager'
import MongoManager from './agent3/mongomanager'
import Os from 'os'
import { Document, MongoClient as DocClient, MongoClientOptions } from 'mongodb'
import UnifiedLogger from './agent3/unifiedLogger'
import { ActionDoc } from './@types/document'
import Agent from './agent3/agent'
import AgentFactory from './agent3/agentFactory'
import AgentsCache from './agent3/agentsCache'

class AgentCluster {
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
  /** Used to execute a run of the simulation each given interval */
  private intervalTimer!: NodeJS.Timer | null

  private agentCache!: AgentsCache
  private hostedAgents!: Agent[]

  constructor(
    myChipsDBConfig: DBConfig,
    worldDBConfig: DBConfig,
    networkConfig: NetworkConfig
  ) {
    this.networkConfig = networkConfig
    this.host = networkConfig.peerServer || Os.hostname()

    // Bind functions we are passing as callbacks (makes sure `this` always refers to this object)
    this.loadInitialUsers = this.loadInitialUsers.bind(this)
    this.notifyOfTallyChange = this.notifyOfTallyChange.bind(this)
    this.notifyOfNewAgentRequest = this.notifyOfNewAgentRequest.bind(this)
    this.notifyOfAgentsChange = this.notifyOfAgentsChange.bind(this)
    this.eatAgents = this.eatAgents.bind(this)
    this.eatParameters = this.eatParameters.bind(this)

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
    this.myChipsDBManager = SQLManager.getInstance(myChipsDBConfig, this.params)
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

    this.agentCache = AgentsCache.getInstance()

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
    this.myChipsDBManager.getParameters(this.eatParameters) //Load initial parameters

    this.worldDBManager.createConnection(
      this.notifyOfNewAgentRequest,
      // loadInitialUsers is called once the connection is created asynchronously
      this.loadInitialUsers
    )

    // Start simulation
    if (this.intervalTimer) clearInterval(this.intervalTimer) // Restart interval timer
    this.intervalTimer = setInterval(() => {
        // If there is no limit on runs, or we're below the limit...
        if (!this.runs || this.runCounter < this.runs) {
          ++this.runCounter
          this.hostedAgents.forEach(this.process)
        }
        else {
          this.close()
        }
      }, this.params.interval)
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

  notifyOfParamsChange(target: string, value: any) {
    this.params[target] = value
  }

  notifyOfTallyChange(message: any) {
    this.logger.debug('Peer Message:', message)

    //Someone is asking an agent to act on a tally
    if (message.state == 'peerProffer') {
      this.logger.verbose('  peerProffer:', message.entity)
      this.hostedAgents.forEach((agent)=>{
        if (agent.id == message.entity) {
          agent.acceptNewConnection(message)
        }
      })
    }
  }

  notifyOfNewAgentRequest(agentData: AgentData, tag: string, destinationHost: string) {
    if (!this.agentCache.containsAgent(agentData)) {
      this.myChipsDBManager.addAgent(agentData)
      this.agentCache.addAgent(agentData)
    }
    this.worldDBManager.insertAction("done", tag, destinationHost)
  }

  // --- Helper Functions --------------------------------------------------------

  // -----------------------------------------------------------------------------
  // Gets the agents from the SQLManager
  eatAgents(dbAgents: AgentData[], all?: boolean) {
    //Freshly load agent data from database
    if (!this.worldDBManager.isDBClientConnected()) {
      //Document db connected/ready
      return
    } 

    dbAgents.forEach((dbAgent) => {
      //For each agent in sql
      this.agentCache.addAgent(dbAgent)
    })

    // Ensure all agents hosted on this server have an Agent object
    let localAgents = dbAgents.filter((val) => val.host == this.host)
    let typesToMake: [string, AdjustableAgentParams?][] = []
    this.params.agentTypes.forEach((agentType) => {
      for (let i = 0; i < Math.round(agentType.percentOfTotal * localAgents.length); i++) {
        typesToMake.push([agentType.type, agentType])
      }
    })

    for (let i = 0; i < localAgents.length - typesToMake.length; i++) {
      typesToMake.push(["default", undefined])
    }
    let hostedAgentIds: string[] = []
    for (let i = 0; i < localAgents.length; i++) {
      let newAgent = AgentFactory.createAgent(typesToMake[i][0], localAgents[i], this.host, typesToMake[i][1])
      newAgent.random = Math.random()
      this.worldDBManager.updateOneAgent(newAgent)
      this.hostedAgents.push(newAgent)
      hostedAgentIds.push(newAgent.peer_cid)
    }

    // If loading all users (loading for the first time)
    if (all) {
      this.worldDBManager.deleteAllAgentsExcept(hostedAgentIds)
    }
  }

  // -----------------------------------------------------------------------------
  //Digest operating parameters from database
  eatParameters(parameters: ParamData[]) {
    this.logger.trace('eatParams')
    parameters.forEach((parameter) => {
      let { name, value } = parameter
      this.params[name] = value
    })
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
      this.runCounter,
      agent.id,
      agent.std_name,
      agent.peer_cid
    )

    agent.takeAction()
    
    this.logger.debug(
      '  stocks:',
      agent.numSpendingTargets,
      '  foils:',
      'action taken:',
      agent.lastActionTaken
    )
  }
}

export = AgentCluster

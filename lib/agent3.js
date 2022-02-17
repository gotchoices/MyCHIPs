"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
const sqlmanager_1 = __importDefault(require("./agent3/sqlmanager"));
const mongomanager_1 = __importDefault(require("./agent3/mongomanager"));
const os_1 = __importDefault(require("os"));
const unifiedLogger_1 = __importDefault(require("./agent3/unifiedLogger"));
const agentFactory_1 = __importDefault(require("./agent3/agentFactory"));
const agentsCache_1 = __importDefault(require("./agent3/agentsCache"));
/**
 * @class AgentCluster
 * Each 'agent' docker container runs an AgentCluster instance
which is in charge of managing the simulation for that container
 * Each AgentCluster instance has exclusive access to its corresponding MyChips database and shared access to the World database.
 * The World database is the means by which the AgentClusters communicate
 with eachother
 * The AgentCluster only has to worry about qualifying and initiating
 credit lifts. The actual heavy lifting occurs automatically within the pg and peers databases once a lift is initated by having the AgentCluster insert accounts into the pg containers.
 */
class AgentCluster {
    constructor(myChipsDBConfig, worldDBConfig, networkConfig) {
        console.log('STARTING AGENT MODEL * VERSION 3 *');
        this.networkConfig = networkConfig;
        this.host = networkConfig.peerServer || os_1.default.hostname();
        // Bind functions we are passing as callbacks (makes sure `this` always refers to this object)
        this.loadInitialUsers = this.loadInitialUsers.bind(this);
        this.notifyOfTallyChange = this.notifyOfTallyChange.bind(this);
        this.notifyOfNewAgentRequest = this.notifyOfNewAgentRequest.bind(this);
        this.notifyOfAgentsChange = this.notifyOfAgentsChange.bind(this);
        this.eatAgents = this.eatAgents.bind(this);
        this.eatParameters = this.eatParameters.bind(this);
        this.process = this.process.bind(this);
        // Initialize agent logger
        this.logger = unifiedLogger_1.default.getInstance();
        this.logger.info('Starting up Account Server v3 on:', this.host);
        // Start setting things up
        this.hostedAgents = [];
        this.loadParamsConfig();
        this.configureDatabases(myChipsDBConfig, worldDBConfig);
        this.run();
    }
    // Loads parameters from the config file
    loadParamsConfig() {
        const fs = require('fs');
        const yaml = require('js-yaml');
        this.logger.debug('Loading parameters from config file');
        try {
            let fileContents = fs.readFileSync(__dirname + '/agent3/paramConfig.yaml');
            this.params = yaml.load(fileContents);
            console.log(this.params);
        }
        catch (e) {
            console.log(e);
            this.logger.error(e);
        }
    }
    configureDatabases(myChipsDBConfig, worldDBConfig) {
        this.logger.debug('Configuring the databases');
        // Configure SQLManager
        this.myChipsDBManager = sqlmanager_1.default.getInstance(myChipsDBConfig, this.params);
        // Configure MongoManager
        this.worldDBManager = mongomanager_1.default.getInstance(worldDBConfig, this.networkConfig);
    }
    // calls run on all of the agents
    run() {
        this.agentCache = agentsCache_1.default.getInstance();
        this.runCounter = 0;
        if (this.networkConfig.runs) {
            this.runs = this.networkConfig.runs;
        } //Max iterations
        this.myChipsDBManager.createConnection(this.notifyOfAgentsChange, this.notifyOfParamsChange, this.notifyOfTallyChange);
        this.intervalTimer = null;
        // TODO: determine if this is necessary with new paramConfig.yaml
        this.myChipsDBManager.getParameters(this.eatParameters); //Load initial parameters
        this.worldDBManager.createConnection(this.notifyOfNewAgentRequest, 
        // loadInitialUsers is called once the connection is created asynchronously
        this.loadInitialUsers);
        //TODO: Right now we're in callback hell, despite our efforts to clean it up. I want to start
        // using the async/await syntax to get rid of all of the callbacks.
        // Because of this, the simulation doesn't start until eatAgents() finishes running for the
        // first time.
    }
    startSimulation() {
        if (this.intervalTimer)
            clearInterval(this.intervalTimer); // Restart interval timer
        this.intervalTimer = setInterval(() => {
            // If there is no limit on runs, or we're below the limit...
            if (!this.runs || this.runCounter < this.runs) {
                ++this.runCounter;
                this.hostedAgents.forEach(this.process);
            }
            else {
                this.close();
            }
        }, this.params.interval);
    }
    // Replaces checkPeer() in agent2
    ensurePeerInSystem() { }
    // --- Functions passed as callbacks -------------------------------------------------------
    /** Callback
     * Loads agents from the MyCHIPs Database
     */
    loadInitialUsers() {
        this.logger.debug('Loading initial accounts');
        this.myChipsDBManager.queryUsers(this.eatAgents); //Load up initial set of users
    }
    // gets agents from SQL and puts hosted agent info into MongoDB
    notifyOfAgentsChange(msg) {
        this.myChipsDBManager.queryLatestUsers(msg.time, this.eatAgents);
    }
    notifyOfParamsChange(target, value) {
        this.params[target] = value;
    }
    notifyOfTallyChange(message) {
        this.logger.debug('Peer Message:', message);
        //Someone is asking an agent to act on a tally
        if (message.state == 'peerProffer') {
            this.logger.verbose('  peerProffer:', message.entity);
            this.hostedAgents.forEach((agent) => {
                if (agent.id == message.entity) {
                    agent.acceptNewConnection(message);
                }
            });
        }
    }
    notifyOfNewAgentRequest(agentData, tag, destinationHost) {
        if (!this.agentCache.containsAgent(agentData)) {
            this.myChipsDBManager.addAgent(agentData);
            this.agentCache.addAgent(agentData);
        }
        this.worldDBManager.insertAction('done', tag, destinationHost);
    }
    // --- Helper Functions --------------------------------------------------------
    // -----------------------------------------------------------------------------
    /** Callback
     * Takes the agents from the MyChipsDBManager and loads them into the worldDB
     *  @param dbAgents - array of agents fetched from MyChips Databases
     * !TODO does this fetch from all databases?
     * @param all - boolean that states whether dbAgents includes all accounts
     */
    eatAgents(dbAgents, all) {
        // Make sure document db is connected and ready
        if (!this.worldDBManager.isDBClientConnected()) {
            return;
        }
        let localAgents = [];
        dbAgents.forEach((dbAgent) => {
            if (dbAgent.user_ent) {
                dbAgent.hosted_ent = true;
                localAgents.push(dbAgent);
            }
            this.agentCache.addAgent(dbAgent);
        });
        // Ensure all agents hosted on this server have an Agent object
        let typesToMake = [];
        this.params.agentTypes.forEach((agentType) => {
            for (let i = 0; i < Math.round(agentType.percentOfTotal * localAgents.length); i++) {
                typesToMake.push([agentType.type, agentType]);
            }
        });
        for (let i = 0; i < localAgents.length - typesToMake.length; i++) {
            typesToMake.push(['default', undefined]);
        }
        let hostedAgentIds = [];
        for (let i = 0; i < localAgents.length; i++) {
            let newAgent = agentFactory_1.default.createAgent(typesToMake[i][0], localAgents[i], this.host, typesToMake[i][1]);
            this.worldDBManager.updateOneAgent(newAgent.getAgentData());
            this.hostedAgents.push(newAgent);
            hostedAgentIds.push(newAgent.peer_cid);
        }
        // If loading all users (loading for the first time)
        if (all) {
            this.worldDBManager.deleteAllAgentsExcept(hostedAgentIds);
            this.startSimulation();
        }
    }
    // -----------------------------------------------------------------------------
    //Digest operating parameters from database
    eatParameters(parameters) {
        this.logger.trace('eatParams');
        parameters.forEach((parameter) => {
            let { name, value } = parameter;
            this.params[name] = value;
        });
    }
    // -----------------------------------------------------------------------------
    //Shut down this controller
    close() {
        this.logger.debug('Shutting down agent handler');
        if (this.myChipsDBManager.isActiveQuery()) {
            //If there is a query in process
            setTimeout(this.close, 500); //Try again in a half second
        }
        else {
            this.myChipsDBManager.closeConnection();
        }
        if (this.intervalTimer)
            clearInterval(this.intervalTimer);
    }
    // -----------------------------------------------------------------------------
    process(agent) {
        //Iterate on a single agent
        // @ts-ignore
        this.logger.verbose('Handler', this.runCounter, agent.id, agent.std_name, agent.peer_cid);
        agent.takeAction();
        this.logger.debug('  stocks:', agent.numSpendingTargets, '  foils:', 'action taken:', agent.lastActionTaken);
    }
}
module.exports = AgentCluster;

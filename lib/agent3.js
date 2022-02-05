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
const WorldDBOpts = { useNewUrlParser: true, useUnifiedTopology: true };
class AgentCluster {
    constructor(myChipsDBConfig, worldDBConfig, networkConfig) {
        this.networkConfig = networkConfig;
        this.host = networkConfig.peerServer || os_1.default.hostname();
        // Bind functions we are passing as callbacks (makes sure `this` always refers to this object)
        this.loadInitialUsers = this.loadInitialUsers.bind(this);
        this.notifyOfTallyChange = this.notifyOfTallyChange.bind(this);
        this.notifyOfNewAgentRequest = this.notifyOfNewAgentRequest.bind(this);
        this.notifyOfAgentsChange = this.notifyOfAgentsChange.bind(this);
        // Initialize agent logger
        this.logger = unifiedLogger_1.default.getInstance();
        this.logger.info('Initializing agent model controller 3 on:', this.host);
        this.loadParamsConfig();
        this.configureDatabases(myChipsDBConfig, worldDBConfig);
        this.run();
    }
    // Loads parameters from the config file
    loadParamsConfig() {
        const fs = require('fs');
        const yaml = require('js-yaml');
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
        // Configure SQLManager
        this.myChipsDBManager = sqlmanager_1.default.getInstance(myChipsDBConfig, this.params);
        // Configure MongoManager
        this.worldDBManager = mongomanager_1.default.getInstance(worldDBConfig, this.networkConfig);
    }
    // calls run on all of the agents
    run() {
        console.log('RUNNING AGENT MODEL * VERSION 3 *');
        this.logger.info('RUNNING AGENT MODEL V3');
        this.agentCache = agentsCache_1.default.getInstance();
        this.runCounter = 0;
        if (this.networkConfig.runs) {
            this.runs = this.networkConfig.runs;
        } //Max iterations
        this.myChipsDBManager.createConnection(this.notifyOfAgentsChange, this.notifyOfParamsChange, this.notifyOfTallyChange);
        this.intervalTimer = null;
        // TODO: determine if this is necessary with new paramConfig.yaml
        this.myChipsDBManager.getParameters(this.eatParameters); //Load initial parameters
        this.worldDBManager.createConnection(WorldDBOpts, this.notifyOfNewAgentRequest, 
        // loadInitialUsers is called once the connection is created asynchronously
        this.loadInitialUsers);
        // Start simulation
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
    // Loads agents from the MyCHIPs Database
    loadInitialUsers() {
        this.myChipsDBManager.queryUsers(this.eatAgents); //Load up initial set of users
    }
    // gets agents from SQL and puts hosted agent info into MongoDB
    notifyOfAgentsChange(msg) {
        this.myChipsDBManager.queryLatestUsers(msg.time, this.eatAgents);
    }
    notifyOfParamsChange(target, value) {
        this.params[target] = value;
    }
    notifyOfTallyChange(msg) {
        this.tallyState(msg);
    }
    notifyOfNewAgentRequest(agentData, tag, destinationHost) {
        if (!this.agentCache.containsAgent(agentData)) {
            this.myChipsDBManager.addAgent(agentData);
            this.agentCache.addAgent(agentData);
        }
        this.worldDBManager.insertAction("done", tag, destinationHost);
    }
    /** As far as I can tell, this method is called when this server is notified (through the peer
     * and pg containers) that someone out there wants to make a tally. It looks like it doesn't
     * even check to see which agent is getting the request, it just accepts. */
    //TODO: Set up way for an agent to accept a tally request for itself instead of the cluster
    // doing the accept for it. Perhaps a new Action to accept a Tally
    tallyState(message) {
        //Someone is asking an agent to act on a tally
        this.logger.debug('Peer Message:', message);
        if (message.state == 'peerProffer') {
            //For now, we will just answer 'yes'
            this.logger.verbose('  peerProffer:', message.entity);
            this.myChipsDBManager.query("update mychips.tallies_v set request = 'open' where tally_ent = $1 and tally_seq = $2", [message.entity, message.sequence], (e, r) => {
                if (e) {
                    this.logger.error('In :', e.stack);
                    return;
                }
                this.logger.verbose('  Tally affirmed:', message.object);
            });
        }
    }
    // --- Helper Functions --------------------------------------------------------
    // -----------------------------------------------------------------------------
    // Gets the agents from the SQLManager
    eatAgents(dbAgents, all) {
        //Freshly load agent data from database
        if (!this.worldDBManager.isDBClientConnected()) {
            //Document db connected/ready
            return;
        }
        let processedAgents = []; //Keep track of which ones we've processed
        dbAgents.forEach((dbAgent) => {
            //For each agent in sql
            this.agentCache.addAgent(dbAgent);
            if (dbAgent.hosted_ent) {
                //If this is one we host, update world db
                processedAgents.push(dbAgent.peer_cid);
                dbAgent.random = Math.random();
                this.worldDBManager.updateOneAgent(dbAgent);
            }
        });
        // If loading all users (loading for the first time)
        if (all) {
            this.worldDBManager.deleteManyAgents(processedAgents);
        }
        // Ensure all agents hosted on this server have an Agent object
        let localAgents = dbAgents.filter((val) => val.host == this.host);
        let typesToMake = [];
        this.params.agentTypes.forEach((agentType) => {
            for (let i = 0; i < Math.round(agentType.percentOfTotal * localAgents.length); i++) {
                typesToMake.push([agentType.type, agentType]);
            }
        });
        for (let i = 0; i < localAgents.length - typesToMake.length; i++) {
            typesToMake.push(["default", undefined]);
        }
        for (let i = 0; i < localAgents.length; i++) {
            this.hostedAgents.push(agentFactory_1.default.createAgent(typesToMake[i][0], localAgents[i], typesToMake[i][1]));
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

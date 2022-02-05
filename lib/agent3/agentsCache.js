"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const unifiedLogger_1 = __importDefault(require("./unifiedLogger"));
class AgentsCache {
    constructor() {
        this.agentCache = {};
        this.logger = unifiedLogger_1.default.getInstance();
    }
    static getInstance() {
        if (!AgentsCache.instance) {
            AgentsCache.instance = new AgentsCache();
        }
        return AgentsCache.instance;
    }
    addAgent(agentData) {
        this.agentCache[agentData.peer_cid] = agentData;
    }
    // Check to see if a peer is in our system, if not add them and then do cb
    containsAgent(targetAgent) {
        let foundAgentData = this.agentCache[targetAgent.peer_cid];
        this.logger.debug('Checking if we have peer:', targetAgent.peer_cid, !!foundAgentData);
        if (foundAgentData) {
            this.logger.debug('Found match for peer', targetAgent.peer_cid, 'in system');
            return true;
        }
        else {
            this.logger.debug('No match found for peer', targetAgent.peer_cid, '. Creating one now.');
            return false;
        }
    }
}
exports.default = AgentsCache;

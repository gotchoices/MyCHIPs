"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const agentsCache_1 = __importDefault(require("../agentsCache"));
const mongomanager_1 = __importDefault(require("../mongomanager"));
const sqlmanager_1 = __importDefault(require("../sqlmanager"));
const unifiedLogger_1 = __importDefault(require("../unifiedLogger"));
class FindNewSpendingSource {
    constructor(agent) {
        this.logger = unifiedLogger_1.default.getInstance();
        this.myChipsDBManager = sqlmanager_1.default.getInstance();
        this.worldDBManager = mongomanager_1.default.getInstance();
        this.agentCache = agentsCache_1.default.getInstance();
        this.agent = agent;
    }
    run() {
        if (this.agent.numSpendingTargets <= 0 || // If the agent has no stocks   or
            (this.agent.numSpendingTargets < this.agent.maxSpendingTargets && // (if the agent doesn't have too many stocks and
                Math.random() < this.agent.newSpendingTargetOdds)) //  we randgomly choose to))
         {
            let newPeer = this.worldDBManager.findPeerAndUpdate(this.agent.peer_cid, this.agent.spendingTargets);
            this.logger.debug(this.agent.peer_cid, "  attempting new spending source with", newPeer.peer_cid);
            // Save new peer data locally
            if (!this.agentCache.containsAgent(newPeer)) {
                this.myChipsDBManager.addAgent(newPeer);
                this.agentCache.addAgent(newPeer);
            }
            // Send new connection request to the potential peer we found
            let newPeerServer = newPeer.peer_socket.split(':')[0];
            this.worldDBManager.insertAction("createAccount", undefined, newPeerServer, () => {
                this.myChipsDBManager.addConnection(this.agent.id, newPeer.id);
                this.agent.numSpendingTargets++;
            });
        }
    }
}
exports.default = FindNewSpendingSource;

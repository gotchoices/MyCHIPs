"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const agentsCache_1 = __importDefault(require("../agentsCache"));
const mongomanager_1 = __importDefault(require("../mongomanager"));
const sqlmanager_1 = __importDefault(require("../sqlmanager"));
const unifiedLogger_1 = __importDefault(require("../unifiedLogger"));
class FindNewSpendingTarget {
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
            console.log("\n", this.agent.peer_cid, "is finding a new spending target!");
            this.worldDBManager.findPeerAndUpdate(this.agent.peer_cid, this.agent.spendingTargets, (newPeer) => {
                console.log(this.agent.peer_cid, "wants to connect to", newPeer.peer_cid);
                console.log("Peer:", newPeer.peer_cid, newPeer.id);
                this.logger.debug(this.agent.peer_cid, "  attempting new spending source with", newPeer.peer_cid);
                // Save new peer data locally
                if (!this.agentCache.containsAgent(newPeer)) {
                    this.myChipsDBManager.addAgent(newPeer);
                    this.agentCache.addAgent(newPeer);
                }
                // See if the peer is on a different server
                let newPeerServer = newPeer.peer_sock.split(':')[0];
                if (newPeerServer != this.agent.host) {
                    // If it is, request that the other server gets our info
                    this.worldDBManager.insertAction("createAccount", undefined, newPeerServer, this.agent.getAgentData(), () => {
                        this.addConnectionRequest(newPeer.id);
                    });
                }
                else {
                    // Otherwise, just made the connection request
                    this.addConnectionRequest(newPeer.id);
                }
            });
        }
    }
    addConnectionRequest(peerID) {
        console.log(this.agent.std_name, "sending connection request to", peerID);
        this.myChipsDBManager.addConnectionRequest(this.agent.id, peerID);
        this.agent.numSpendingTargets++;
        this.worldDBManager.updateOneAgent(this.agent.getAgentData());
    }
}
exports.default = FindNewSpendingTarget;

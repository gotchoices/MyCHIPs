"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const agentsCache_1 = __importDefault(require("../agentsCache"));
const mongomanager_1 = __importDefault(require("../mongomanager"));
const sqlmanager_1 = __importDefault(require("../sqlmanager"));
const unifiedLogger_1 = __importDefault(require("../unifiedLogger"));
class FindNewIncomeSource {
    constructor(agent) {
        this.logger = unifiedLogger_1.default.getInstance();
        this.myChipsDBManager = sqlmanager_1.default.getInstance();
        this.worldDBManager = mongomanager_1.default.getInstance();
        this.agentCache = agentsCache_1.default.getInstance();
        this.agent = agent;
    }
    run() {
        if (this.agent.numIncomeSources <= 0 ||
            (this.agent.numIncomeSources < this.agent.maxIncomeSources &&
                Math.random() < this.agent.newIncomeSourceOdds)) {
            this.worldDBManager.findPeerAndUpdate(this.agent.peer_cid, this.agent.incomeSources, (newPeer) => {
                this.logger.debug(this.agent.peer_cid, " attempting new income source with ", newPeer.peer_cid);
                if (!this.agentCache.containsAgent(newPeer)) {
                    this.myChipsDBManager.addAgent(newPeer);
                    this.agentCache.addAgent(newPeer);
                }
                let newPeerServer = newPeer.peer_sock.split(':')[0];
                this.worldDBManager.insertAction("createAccount", undefined, newPeerServer, () => {
                    this.myChipsDBManager.addConnectionRequest(this.agent.id, newPeer.id);
                    // TODO: This stuff should only be done when the connection is accepted by the peer. Right now the peers always accept requests, so we can do it here. I'm not sure how we will get notified when the connection is accepted...
                    this.agent.numIncomeSources++;
                    this.worldDBManager.updateOneAgent(this.agent.getAgentData());
                });
            });
        }
    }
}
exports.default = FindNewIncomeSource;

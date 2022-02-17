"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const agentsCache_1 = __importDefault(require("../agentsCache"));
const mongomanager_1 = __importDefault(require("../mongomanager"));
const sqlmanager_1 = __importDefault(require("../sqlmanager"));
const unifiedLogger_1 = __importDefault(require("../unifiedLogger"));
class SpendCHIPs {
    constructor(agent) {
        this.logger = unifiedLogger_1.default.getInstance();
        this.myChipsDBManager = sqlmanager_1.default.getInstance();
        this.worldDBManager = mongomanager_1.default.getInstance();
        this.agentCache = agentsCache_1.default.getInstance();
        this.agent = agent;
    }
    run() {
        if (this.agent.numSpendingTargets > 0 && this.agent.netWorth > this.agent.minWorthToSpend) {
            let chipsToSpend = Math.floor(Math.random() * Math.max(this.agent.netWorth * this.agent.maxToSpend, 1000));
            let peerToPayID = this.agent.spendingTargets[Math.floor(Math.random() * this.agent.numSpendingTargets)];
            let peerToPay = this.agentCache.getAgent(peerToPayID);
            let sequence = this.agent.foil_seqs[peerToPayID];
            this.myChipsDBManager.addPayment(this.agent.id, peerToPay.id, chipsToSpend, sequence);
        }
    }
}
exports.default = SpendCHIPs;

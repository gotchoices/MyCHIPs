"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const mongomanager_1 = __importDefault(require("../mongomanager"));
const sqlmanager_1 = __importDefault(require("../sqlmanager"));
const actionFactory_1 = __importDefault(require("../actionFactory"));
const unifiedLogger_1 = __importDefault(require("../unifiedLogger"));
class BaseAgent {
    constructor(agentData, host, agentParams) {
        this.worldDBManager = mongomanager_1.default.getInstance();
        this.myChipsDBManager = sqlmanager_1.default.getInstance();
        this.logger = unifiedLogger_1.default.getInstance();
        //TODO these need to have actual parameters for the factory
        this.actions = [];
        this.actions.push(actionFactory_1.default.createAction('NewSpendingSource', this));
        // this.actions.push(ActionFactory.createAction('NewIncomeSource', this)); // Not correctly implemented yet 
        this.actions.push(actionFactory_1.default.createAction('SpendCHIPs', this));
        //TODO: finish applying this info from agent data and params
        this.id = agentData.id;
        this.std_name = agentData.std_name;
        this.peer_cid = agentData.peer_cid;
        this.host = host;
        this.numSpendingTargets = 0;
        this.numIncomeSources = 0;
        this.foil_seq = agentData.foil_seqs;
        this.netWorth = 0;
        this.hosted_ent = true;
        this.lastActionTaken = '';
        this.spendingTargets = [];
        this.incomeSources = [];
        this.seqs = [];
        this.types = [];
        this.newIncomeSourceOdds = (agentParams === null || agentParams === void 0 ? void 0 : agentParams.newIncomeSourceOdds) || 0.1;
        this.adjustSettingsOdds = (agentParams === null || agentParams === void 0 ? void 0 : agentParams.adjustSettingsOdds) || 0.5;
        this.newSpendingTargetOdds = (agentParams === null || agentParams === void 0 ? void 0 : agentParams.newSpendingTargetOdds) || 0.15;
        this.maxSpendingTargets = (agentParams === null || agentParams === void 0 ? void 0 : agentParams.maxSpendingTargets) || 2;
        this.maxIncomeSources = (agentParams === null || agentParams === void 0 ? void 0 : agentParams.maxIncomeSources) || 3;
        this.minWorthToSpend = (agentParams === null || agentParams === void 0 ? void 0 : agentParams.minWorthToSpend) || -10000;
        this.maxToSpend = (agentParams === null || agentParams === void 0 ? void 0 : agentParams.maxToSpend) || 0.1;
    }
    takeAction() {
        // For now, I'm just having the Agent perform all of its Actions. Since there's a percentage
        // associated with each Action that determines how likely it is to actually happen, I think
        // this is ok.
        this.actions.forEach((action) => {
            action.run();
        });
    }
    acceptNewConnection(message) {
        // I don't know how to tell the difference between types of connections (whether this account is the income source or spending target)
        // As a default Account, we will always accept a connection
        this.myChipsDBManager.updateConnectionRequest(message.entity, message.sequence, true);
        // TODO: update data here (depends on what kind of connection it is though...)
    }
}
exports.default = BaseAgent;

"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const mongoWorldManager_1 = __importDefault(require("../mongoWorldManager"));
const sqlmanager_1 = __importDefault(require("../sqlmanager"));
const actionFactory_1 = __importDefault(require("../actionFactory"));
const unifiedLogger_1 = __importDefault(require("../unifiedLogger"));
class BaseAccount {
    constructor(accountData, host, accountParams) {
        this.worldDBManager = mongoWorldManager_1.default.getInstance();
        this.myChipsDBManager = sqlmanager_1.default.getInstance();
        this.logger = unifiedLogger_1.default.getInstance();
        this.logger.trace('Creating account object for', accountData.std_name);
        //TODO these need to have actual parameters for the factory
        this.actions = [];
        this.actions.push(actionFactory_1.default.createAction('NewSpendingSource', this));
        // this.actions.push(ActionFactory.createAction('NewIncomeSource', this)); // Not correctly implemented yet
        this.actions.push(actionFactory_1.default.createAction('SpendCHIPs', this));
        this.actions.push(actionFactory_1.default.createAction('AskForLift', this));
        this.id = accountData.id;
        this.std_name = accountData.std_name;
        this.ent_name = accountData.ent_name;
        this.first_name = accountData.fir_name;
        this.peer_cid = accountData.peer_cid;
        this.agent = accountData.peer_agent;
        this.certificate = accountData.cert;
        this.host = accountData.peer_host || host;
        this.port = accountData.peer_port;
        this.entity_type = accountData.ent_type || 'p';
        this.random = Math.random();
        this.satisfied = false;
        this.numSpendingTargets = accountData.foils || 0;
        this.foilSequenceNums = accountData.foil_seqs || [];
        this.spendingTargets = accountData.vendors || [];
        this.spendingTargetCids = accountData.vendor_cids || [];
        this.spendingTargetAgents = accountData.vendor_agents || [];
        this.numIncomeSources = accountData.stocks || 0;
        this.stockSequenceNums = accountData.stock_seqs || [];
        this.incomeSources = accountData.clients || [];
        this.incomeSourceCids = accountData.client_cids || [];
        this.incomeSourceAgents = accountData.client_agents || [];
        this.partnerCids = accountData.part_cids || [];
        this.targets = accountData.targets || [];
        this.sequenceNums = accountData.seqs || [];
        this.tallyTypes = accountData.types || [];
        this.netWorth = +accountData.net || 0;
        this.newIncomeSourceOdds = (accountParams === null || accountParams === void 0 ? void 0 : accountParams.newIncomeSourceOdds) || 0.1;
        this.adjustSettingsOdds = (accountParams === null || accountParams === void 0 ? void 0 : accountParams.adjustSettingsOdds) || 0.5;
        this.newSpendingTargetOdds = (accountParams === null || accountParams === void 0 ? void 0 : accountParams.newSpendingTargetOdds) || 0.15;
        this.maxSpendingTargets = (accountParams === null || accountParams === void 0 ? void 0 : accountParams.maxSpendingTargets) || 2;
        this.desiredSpendingTargets = (accountParams === null || accountParams === void 0 ? void 0 : accountParams.desiredSpendingTargets) || 2;
        this.maxIncomeSources = (accountParams === null || accountParams === void 0 ? void 0 : accountParams.maxIncomeSources) || 3;
        this.desiredIncomeSources = (accountParams === null || accountParams === void 0 ? void 0 : accountParams.desiredIncomeSources) || 1;
        this.minWorthToSpend = (accountParams === null || accountParams === void 0 ? void 0 : accountParams.minWorthToSpend) || -10000;
        this.maxToSpend = (accountParams === null || accountParams === void 0 ? void 0 : accountParams.maxToSpend) || 0.1;
        this.diffForLift = (accountParams === null || accountParams === void 0 ? void 0 : accountParams.diffForLift) || 30;
        this.minForSatisfaction = (accountParams === null || accountParams === void 0 ? void 0 : accountParams.minForSatisfaction) || 5;
    }
    takeAction() {
        // For now, I'm just having the Account perform all of its Actions. Since there's a percentage
        // associated with each Action that determines how likely it is to actually happen, I think
        // this is ok.
        this.actions.forEach((action) => {
            action.run();
        });
        this.calculateSatisfaction();
    }
    acceptNewConnection(message) {
        // I don't know how to tell the difference between types of connections (whether this account is the income source or spending target)
        // As a default Account, we will always accept a connection
        this.logger.debug(this.peer_cid, 'is accepting a connection request!');
        this.myChipsDBManager.updateConnectionRequest(message.entity, message.sequence, true);
        // TODO: update data here (depends on what kind of connection it is though...)
    }
    calculateSatisfaction() {
        if (this.numSpendingTargets >= this.desiredSpendingTargets &&
            this.numIncomeSources >= this.desiredIncomeSources &&
            this.netWorth >= this.minForSatisfaction) {
            this.satisfied = true;
        }
        else
            this.satisfied = false;
    }
    updateAccountData(accountData) {
        this.logger.trace(this.peer_cid, 'is getting updated info');
        this.id = accountData.id;
        this.std_name = accountData.std_name;
        this.ent_name = accountData.ent_name;
        this.first_name = accountData.fir_name;
        this.peer_cid = accountData.peer_cid;
        this.agent = accountData.peer_agent;
        this.certificate = accountData.cert;
        this.host = accountData.peer_host;
        this.port = accountData.peer_port;
        this.entity_type = accountData.ent_type;
        this.random = Math.random();
        this.numSpendingTargets = accountData.foils;
        this.spendingTargets = accountData.vendors;
        this.spendingTargetCids = accountData.vendor_cids || [];
        this.foilSequenceNums = accountData.foil_seqs;
        this.spendingTargetAgents = accountData.vendor_agents || [];
        this.numIncomeSources = accountData.stocks;
        this.incomeSources = accountData.clients;
        this.incomeSourceCids = accountData.client_cids || [];
        this.stockSequenceNums = accountData.stock_seqs;
        this.incomeSourceAgents = accountData.client_agents || [];
        this.partnerCids = accountData.part_cids;
        this.targets = accountData.targets || [];
        this.sequenceNums = accountData.seqs;
        this.tallyTypes = accountData.types || [];
        this.netWorth = +accountData.net;
    }
    getAccountData() {
        return {
            id: this.id,
            std_name: this.std_name,
            ent_name: this.ent_name,
            fir_name: this.first_name,
            ent_type: this.entity_type,
            user_ent: this.id,
            peer_cid: this.peer_cid,
            peer_host: this.host,
            peer_agent: this.agent,
            peer_port: this.port,
            cert: this.certificate,
            random: this.random,
            stocks: this.numIncomeSources,
            clients: this.incomeSources,
            client_cids: this.incomeSourceCids,
            stock_seqs: this.stockSequenceNums,
            client_agents: this.incomeSourceAgents,
            foils: this.numSpendingTargets,
            vendors: this.spendingTargets,
            vendor_cids: this.spendingTargetCids,
            foil_seqs: this.foilSequenceNums,
            vendor_agents: this.spendingTargetAgents,
            part_cids: this.partnerCids,
            targets: this.targets,
            types: this.tallyTypes,
            net: this.netWorth,
            seqs: this.sequenceNums,
        };
    }
    getAccountAnalytics() {
        this.calculateSatisfaction();
        return {
            name: this.std_name,
            peer_cid: this.peer_cid,
            id: this.id,
            stocks: this.numIncomeSources,
            foils: this.numSpendingTargets,
            netWorth: this.netWorth,
            satisfied: this.satisfied,
        };
    }
}
exports.default = BaseAccount;

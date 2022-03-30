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
        console.log('Creating account object for', accountData.std_name);
        this.worldDBManager = mongoWorldManager_1.default.getInstance();
        this.myChipsDBManager = sqlmanager_1.default.getInstance();
        this.logger = unifiedLogger_1.default.getInstance();
        //TODO these need to have actual parameters for the factory
        this.actions = [];
        this.actions.push(actionFactory_1.default.createAction('NewSpendingSource', this));
        // this.actions.push(ActionFactory.createAction('NewIncomeSource', this)); // Not correctly implemented yet
        this.actions.push(actionFactory_1.default.createAction('SpendCHIPs', this));
        this.id = accountData.id;
        this.std_name = accountData.std_name;
        this.ent_name = accountData.ent_name;
        this.first_name = accountData.fir_name;
        this.peer_cid = accountData.peer_cid;
        this.peer_socket = accountData.peer_sock;
        this.host = host;
        this.entity_type = accountData.ent_type || 'p';
        this.birthday = accountData.born_date || 'yesterday';
        this.random = Math.random();
        this.numSpendingTargets = 0;
        this.numIncomeSources = 0;
        this.foil_seqs = accountData.foil_seqs || [];
        this.stock_seqs = accountData.stock_seqs || [];
        this.netWorth = 0;
        this.hosted_ent = true;
        this.lastActionTaken = '';
        this.spendingTargets = [];
        this.spendingTargetCids = [];
        this.incomeSources = [];
        this.incomeSourceCids = [];
        this.types = [];
        this.newIncomeSourceOdds = (accountParams === null || accountParams === void 0 ? void 0 : accountParams.newIncomeSourceOdds) || 0.1;
        this.adjustSettingsOdds = (accountParams === null || accountParams === void 0 ? void 0 : accountParams.adjustSettingsOdds) || 0.5;
        this.newSpendingTargetOdds = (accountParams === null || accountParams === void 0 ? void 0 : accountParams.newSpendingTargetOdds) || 0.15;
        this.maxSpendingTargets = (accountParams === null || accountParams === void 0 ? void 0 : accountParams.maxSpendingTargets) || 2;
        this.maxIncomeSources = (accountParams === null || accountParams === void 0 ? void 0 : accountParams.maxIncomeSources) || 3;
        this.minWorthToSpend = (accountParams === null || accountParams === void 0 ? void 0 : accountParams.minWorthToSpend) || -10000;
        this.maxToSpend = (accountParams === null || accountParams === void 0 ? void 0 : accountParams.maxToSpend) || 0.1;
    }
    takeAction() {
        // For now, I'm just having the Account perform all of its Actions. Since there's a percentage
        // associated with each Action that determines how likely it is to actually happen, I think
        // this is ok.
        this.actions.forEach((action) => {
            action.run();
        });
    }
    acceptNewConnection(message) {
        // I don't know how to tell the difference between types of connections (whether this account is the income source or spending target)
        // As a default Account, we will always accept a connection
        console.log(this.peer_cid, 'is accepting a connection request!');
        this.myChipsDBManager.updateConnectionRequest(message.entity, message.sequence, true);
        // TODO: update data here (depends on what kind of connection it is though...)
    }
    updateAccountData(accountData) {
        console.log(this.peer_cid, 'is getting updated info');
        this.id = accountData.id;
        this.std_name = accountData.std_name;
        this.ent_name = accountData.ent_name;
        this.first_name = accountData.fir_name;
        this.peer_cid = accountData.peer_cid;
        this.peer_socket = accountData.peer_sock;
        this.entity_type = accountData.ent_type || 'p';
        this.birthday = accountData.born_date || 'yesterday';
        this.random = Math.random();
        this.numSpendingTargets = accountData.stocks;
        this.numIncomeSources = accountData.foils;
        this.foil_seqs = accountData.foil_seqs;
        this.stock_seqs = accountData.stock_seqs;
        this.netWorth = accountData.units;
        this.hosted_ent = true;
        this.spendingTargets = accountData.vendors;
        this.spendingTargetCids = accountData.vendor_cids || [];
        this.incomeSources = accountData.clients;
        this.incomeSourceCids = accountData.client_cids || [];
        this.types = accountData.types || [];
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
            peer_sock: this.peer_socket,
            born_date: this.birthday,
            stocks: this.numIncomeSources,
            foils: this.numSpendingTargets,
            partners: [...this.spendingTargets, ...this.incomeSources],
            vendors: this.spendingTargets,
            clients: this.incomeSources,
            vendor_cids: this.spendingTargetCids,
            client_cids: this.incomeSourceCids,
            stock_seqs: this.stock_seqs,
            foil_seqs: this.foil_seqs,
            units: this.netWorth,
            seqs: [...this.stock_seqs, ...this.foil_seqs],
            random: this.random,
            host: this.host,
        };
    }
}
exports.default = BaseAccount;

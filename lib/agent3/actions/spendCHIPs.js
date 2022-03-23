"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const accountsCache_1 = __importDefault(require("../accountsCache"));
const mongoWorldManager_1 = __importDefault(require("../mongoWorldManager"));
const sqlmanager_1 = __importDefault(require("../sqlmanager"));
const unifiedLogger_1 = __importDefault(require("../unifiedLogger"));
class SpendCHIPs {
    constructor(account) {
        this.logger = unifiedLogger_1.default.getInstance();
        this.myChipsDBManager = sqlmanager_1.default.getInstance();
        this.worldDBManager = mongoWorldManager_1.default.getInstance();
        this.accountCache = accountsCache_1.default.getInstance();
        this.account = account;
    }
    run() {
        if (this.account.numSpendingTargets > 0 &&
            this.account.netWorth > this.account.minWorthToSpend) {
            console.log(this.account.peer_cid, 'is spending some CHIPs');
            let chipsToSpend = Math.floor(Math.random() *
                Math.max(this.account.netWorth * this.account.maxToSpend, 1000));
            let peerIndex = Math.floor(Math.random() * this.account.numSpendingTargets);
            console.log('index:', peerIndex);
            console.log('ids:', this.account.spendingTargets);
            console.log('cids:', this.account.spendingTargetCids);
            let peerToPayID = this.account.spendingTargets[peerIndex];
            let peerToPayCID = this.account.spendingTargetCids[peerIndex];
            console.log('\tAccount to pay:', peerToPayCID);
            console.log('\tAmount to pay:', chipsToSpend);
            let sequence = this.account.foil_seqs[peerIndex];
            console.log('\tFoil sequence:', sequence);
            this.myChipsDBManager.addPayment(this.account.id, peerToPayID, chipsToSpend, sequence);
        }
    }
}
exports.default = SpendCHIPs;

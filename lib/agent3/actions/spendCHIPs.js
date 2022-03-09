"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const accountsCache_1 = __importDefault(require("../accountsCache"));
const mongomanager_1 = __importDefault(require("../mongomanager"));
const sqlmanager_1 = __importDefault(require("../sqlmanager"));
const unifiedLogger_1 = __importDefault(require("../unifiedLogger"));
class SpendCHIPs {
    constructor(account) {
        this.logger = unifiedLogger_1.default.getInstance();
        this.myChipsDBManager = sqlmanager_1.default.getInstance();
        this.worldDBManager = mongomanager_1.default.getInstance();
        this.accountCache = accountsCache_1.default.getInstance();
        this.account = account;
    }
    run() {
        if (this.account.numSpendingTargets > 0 && this.account.netWorth > this.account.minWorthToSpend) {
            console.log(this.account.peer_cid, "is spending some CHIPs");
            let chipsToSpend = Math.floor(Math.random() * Math.max(this.account.netWorth * this.account.maxToSpend, 1000));
            let peerToPayID = this.account.spendingTargets[Math.floor(Math.random() * this.account.numSpendingTargets)];
            console.log("\tAccount to pay:", peerToPayID);
            console.log("\tAmount to pay:", chipsToSpend);
            let peerToPay = this.accountCache.getAccount(peerToPayID);
            let sequence = this.account.foil_seqs[peerToPayID];
            this.myChipsDBManager.addPayment(this.account.id, peerToPay.id, chipsToSpend, sequence);
        }
    }
}
exports.default = SpendCHIPs;

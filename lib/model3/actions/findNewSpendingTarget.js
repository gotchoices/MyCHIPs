"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const mongoWorldManager_1 = __importDefault(require("../mongoWorldManager"));
const sqlmanager_1 = __importDefault(require("../sqlmanager"));
const unifiedLogger_1 = __importDefault(require("../unifiedLogger"));
class FindNewSpendingTarget {
    constructor(account) {
        this.logger = unifiedLogger_1.default.getInstance();
        this.myChipsDBManager = sqlmanager_1.default.getInstance();
        this.worldDBManager = mongoWorldManager_1.default.getInstance();
        this.account = account;
    }
    // 1. Find peer in world DB (mongo)
    // 2. Send the Connection Request
    run() {
        if (this.account.numSpendingTargets <= 0 || // If the account has no stocks   or
            (this.account.numSpendingTargets < this.account.maxSpendingTargets && // (if the account doesn't have too many stocks and
                Math.random() < this.account.newSpendingTargetOdds)) {
            //  we randomly choose to))
            this.logger.debug(`${this.account.peer_cid} is finding a new spending target!`);
            this.worldDBManager.findPeerAndUpdate(this.account.peer_cid, this.account.spendingTargetCids, (newPeer) => {
                this.logger.debug(this.account.peer_cid, '  attempting new spending source with', newPeer.peer_cid);
                this.myChipsDBManager.addConnectionRequest(this.account.id, this.account.certificate, newPeer.cert);
            });
        }
    }
}
exports.default = FindNewSpendingTarget;

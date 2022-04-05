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
    // 2. Do we have the peer's info already downloaded?
    //	a. If yes, look up the peer's ID in our cache
    //	b. If not, add peer to our MyCHIPs DB (PG)
    //		This gives the peer a new ID on our server (different than their ID on their server)
    // 3. If they are on a different server, ask them to download our info to their server
    // 4. When our info is on the peer's server...
    // 4. Use the peer's ID (not peer_cid) to make a connection (tally) request
    run() {
        if (this.account.numSpendingTargets <= 0 || // If the account has no stocks   or
            (this.account.numSpendingTargets < this.account.maxSpendingTargets && // (if the account doesn't have too many stocks and
                Math.random() < this.account.newSpendingTargetOdds)) {
            //  we randomly choose to))
            console.log(`\t${this.account.peer_cid} is finding a new spending target!`);
            this.worldDBManager.findPeerAndUpdate(this.account.peer_cid, this.account.spendingTargetCids, (newPeer) => {
                console.log(`${this.account.peer_cid} wants to connect to ${newPeer.peer_cid} on ${newPeer.peer_host}`);
                this.logger.debug(this.account.peer_cid, '  attempting new spending source with', newPeer.peer_cid);
                this.myChipsDBManager.addConnectionRequest(this.account.id, this.account.certificate, newPeer.cert);
            });
        }
    }
}
exports.default = FindNewSpendingTarget;

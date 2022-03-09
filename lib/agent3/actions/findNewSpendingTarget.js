"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const accountsCache_1 = __importDefault(require("../accountsCache"));
const mongomanager_1 = __importDefault(require("../mongomanager"));
const sqlmanager_1 = __importDefault(require("../sqlmanager"));
const unifiedLogger_1 = __importDefault(require("../unifiedLogger"));
class FindNewSpendingTarget {
    constructor(account) {
        this.logger = unifiedLogger_1.default.getInstance();
        this.myChipsDBManager = sqlmanager_1.default.getInstance();
        this.worldDBManager = mongomanager_1.default.getInstance();
        this.accountCache = accountsCache_1.default.getInstance();
        this.account = account;
    }
    run() {
        if (this.account.numSpendingTargets <= 0 || // If the account has no stocks   or
            (this.account.numSpendingTargets < this.account.maxSpendingTargets && // (if the account doesn't have too many stocks and
                Math.random() < this.account.newSpendingTargetOdds)) //  we randgomly choose to))
         {
            console.log("\n", this.account.peer_cid, "is finding a new spending target!");
            this.worldDBManager.findPeerAndUpdate(this.account.peer_cid, this.account.spendingTargetCids, (newPeer) => {
                console.log(this.account.peer_cid, "wants to connect to", newPeer.peer_cid);
                console.log("Peer:", newPeer.peer_cid, newPeer.id);
                this.logger.debug(this.account.peer_cid, "  attempting new spending source with", newPeer.peer_cid);
                // Save new peer data locally
                if (!this.accountCache.containsAccount(newPeer)) {
                    this.myChipsDBManager.addAccount(newPeer);
                    this.accountCache.addAccount(newPeer);
                }
                // See if the peer is on a different server
                let newPeerServer = newPeer.peer_sock.split(':')[0];
                if (newPeerServer != this.account.host) {
                    // If it is, request that the other server gets our info
                    this.worldDBManager.insertAction("createAccount", undefined, newPeerServer, this.account.getAccountData(), () => {
                        this.addConnection(newPeer.id, newPeer.peer_cid);
                    });
                }
                else {
                    // Otherwise, just made the connection request
                    this.addConnection(newPeer.id, newPeer.peer_cid);
                }
            });
        }
    }
    addConnection(peer_id, peer_cid) {
        console.log(this.account.std_name, "sending connection request to", peer_cid);
        this.myChipsDBManager.addConnectionRequest(this.account.id, peer_id);
        this.account.numSpendingTargets++;
        if (peer_cid in this.account.spendingTargetCids) {
            this.account.spendingTargetCids.push(peer_cid);
        }
        this.worldDBManager.updateOneAccount(this.account.getAccountData());
    }
}
exports.default = FindNewSpendingTarget;

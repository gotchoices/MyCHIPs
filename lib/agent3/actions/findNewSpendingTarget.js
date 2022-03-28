"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const accountsCache_1 = __importDefault(require("../accountsCache"));
const mongoWorldManager_1 = __importDefault(require("../mongoWorldManager"));
const sqlmanager_1 = __importDefault(require("../sqlmanager"));
const unifiedLogger_1 = __importDefault(require("../unifiedLogger"));
class FindNewSpendingTarget {
    constructor(account) {
        this.logger = unifiedLogger_1.default.getInstance();
        this.myChipsDBManager = sqlmanager_1.default.getInstance();
        this.worldDBManager = mongoWorldManager_1.default.getInstance();
        this.accountCache = accountsCache_1.default.getInstance();
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
            console.log(`\n${this.account.peer_cid} is finding a new spending target!`);
            this.worldDBManager.findPeerAndUpdate(this.account.peer_cid, this.account.spendingTargetCids, (newPeer) => {
                console.log(`${this.account.peer_cid} wants to connect to ${newPeer.peer_cid}`);
                console.log(`Peer from mongo: ${newPeer.peer_cid} ${newPeer.id} on 
            ${newPeer.peer_sock.split(':')[0]}`);
                this.logger.debug(this.account.peer_cid, '  attempting new spending source with', newPeer.peer_cid);
                // TODO: Clean this up...
                // If not in our local cache, give them a new id for our local server
                if (!this.accountCache.containsAccount(newPeer)) {
                    this.myChipsDBManager.addPeerAccount(newPeer, (newLocalPeer) => {
                        console.log(`Peer ${newLocalPeer.peer_cid} now has id:
                ${newLocalPeer.id}`);
                        // See if the peer is on a different server
                        let newPeerServer = newLocalPeer.peer_sock.split(':')[0];
                        if (newPeerServer != this.account.host) {
                            // If it is, request that the other server gets our info
                            this.worldDBManager.insertAction('createAccount', undefined, newPeerServer, this.account.getAccountData(), () => {
                                this.addConnection(newLocalPeer.id, newLocalPeer.peer_cid);
                            });
                        }
                        else {
                            // Otherwise, just made the connection request
                            this.addConnection(newLocalPeer.id, newLocalPeer.peer_cid);
                        }
                    });
                }
                else {
                    newPeer = this.accountCache.getAccountByCID(newPeer.peer_cid);
                    let newPeerServer = newPeer.peer_sock.split(':')[0];
                    if (newPeerServer != this.account.host) {
                        // If it is, request that the other server gets our info
                        this.worldDBManager.insertAction('createAccount', undefined, newPeerServer, this.account.getAccountData(), () => {
                            this.addConnection(newPeer.id, newPeer.peer_cid);
                        });
                    }
                    else {
                        // Otherwise, just made the connection request
                        this.addConnection(newPeer.id, newPeer.peer_cid);
                    }
                }
            });
        }
    }
    addConnection(peer_id, peer_cid) {
        console.log(`${this.account.peer_cid} (${this.account.id}) 
      sending connection request to ${peer_cid} (${peer_id})`);
        this.myChipsDBManager.addConnectionRequest(this.account.id, peer_id);
        //TODO make this depend on being accepted
        this.account.numSpendingTargets++;
        if (!this.account.spendingTargetCids.includes(peer_cid)) {
            console.log(this.account.peer_cid, 'is adding', peer_cid, 'to their lists');
            this.account.spendingTargets.push(peer_id);
            this.account.spendingTargetCids.push(peer_cid);
        }
        console.log(this.account.peer_cid, 'now has', this.account.numSpendingTargets, 'spending targets:\n', this.account.spendingTargetCids);
        this.worldDBManager.updateOneAccount(this.account.getAccountData());
    }
}
exports.default = FindNewSpendingTarget;

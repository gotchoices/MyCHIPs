"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const accountsCache_1 = __importDefault(require("../accountsCache"));
const mongoWorldManager_1 = __importDefault(require("../mongoWorldManager"));
const sqlmanager_1 = __importDefault(require("../sqlmanager"));
const unifiedLogger_1 = __importDefault(require("../unifiedLogger"));
class FindNewIncomeSource {
    constructor(account) {
        this.logger = unifiedLogger_1.default.getInstance();
        this.myChipsDBManager = sqlmanager_1.default.getInstance();
        this.worldDBManager = mongoWorldManager_1.default.getInstance();
        this.accountCache = accountsCache_1.default.getInstance();
        this.account = account;
    }
    run() {
        if (this.account.numIncomeSources <= 0 ||
            (this.account.numIncomeSources < this.account.maxIncomeSources &&
                Math.random() < this.account.newIncomeSourceOdds)) {
            this.worldDBManager.findPeerAndUpdate(this.account.peer_cid, this.account.incomeSources, (newPeer) => {
                this.logger.debug(this.account.peer_cid, ' attempting new income source with ', newPeer.peer_cid);
                if (!this.accountCache.containsAccount(newPeer)) {
                    this.myChipsDBManager.addPeerAccount(newPeer);
                    this.accountCache.addAccount(newPeer);
                }
                let newPeerServer = newPeer.peer_sock.split(':')[0];
                this.worldDBManager.insertAction('createAccount', undefined, newPeerServer, () => {
                    this.myChipsDBManager.addConnectionRequest(this.account.id, newPeer.id);
                    // TODO: This stuff should only be done when the connection is accepted by the peer. Right now the peers always accept requests, so we can do it here. I'm not sure how we will get notified when the connection is accepted...
                    this.account.numIncomeSources++;
                    this.worldDBManager.updateOneAccount(this.account.getAccountData());
                });
            });
        }
    }
}
exports.default = FindNewIncomeSource;

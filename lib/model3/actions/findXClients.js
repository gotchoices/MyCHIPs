"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const sqlmanager_1 = __importDefault(require("../sqlmanager"));
const mongoWorldManager_1 = __importDefault(require("../mongoWorldManager"));
const unifiedLogger_1 = __importDefault(require("../unifiedLogger"));
class FindXClients {
    constructor(account, numClients) {
        this.logger = unifiedLogger_1.default.getInstance();
        this.myChipsDBManager = sqlmanager_1.default.getInstance();
        this.worldDBManager = mongoWorldManager_1.default.getInstance();
        this.account = account;
        this.numClients = numClients;
    }
    run() {
        if (this.account.numIncomeSources <= 0 ||
            this.account.numIncomeSources < this.account.maxIncomeSources) {
            for (var i = this.numClients; i <= this.numClients; --i) {
                this.worldDBManager.findPeerAndUpdate(this.account.peer_cid, this.account.incomeSources, (newPeer) => {
                    this.logger.debug('retailer: ', this.account.peer_cid, ' attempting new client with ', newPeer.peer_cid);
                });
            }
        }
    }
}

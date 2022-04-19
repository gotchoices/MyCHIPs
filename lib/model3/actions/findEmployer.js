"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const sqlmanager_1 = __importDefault(require("../sqlmanager"));
const mongoWorldManager_1 = __importDefault(require("../mongoWorldManager"));
const unifiedLogger_1 = __importDefault(require("../unifiedLogger"));
const baseAccount_1 = __importDefault(require("../accounts/baseAccount"));
class FindEmployer {
    constructor(account, numClients) {
        this.logger = unifiedLogger_1.default.getInstance();
        this.myChipsDBManager = sqlmanager_1.default.getInstance();
        this.worldDBManager = mongoWorldManager_1.default.getInstance();
        this.account = account;
        this.numClients = numClients;
    }
    run() {
        this.worldDBManager.findPeerAndUpdate(this.account.peer_cid, this.account.incomeSources, (newPeer) => {
            this.logger.debug('employee: ', this.account.peer_cid, ' attempting new employer with ', newPeer.peer_cid);
            this.account.changeEmployer(new baseAccount_1.default(newPeer, newPeer.peer_host, undefined));
        });
        //Request chips based on sallary from new employer
    }
}
exports.default = FindEmployer;

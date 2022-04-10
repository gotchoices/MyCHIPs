"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const mongoWorldManager_1 = __importDefault(require("../mongoWorldManager"));
const sqlmanager_1 = __importDefault(require("../sqlmanager"));
const unifiedLogger_1 = __importDefault(require("../unifiedLogger"));
//TODO: This class is borken! Fix it using FindNewSpendingTarget as a template.
class FindNewIncomeSource {
    constructor(account) {
        this.logger = unifiedLogger_1.default.getInstance();
        this.myChipsDBManager = sqlmanager_1.default.getInstance();
        this.worldDBManager = mongoWorldManager_1.default.getInstance();
        this.account = account;
    }
    run() {
        if (this.account.numIncomeSources <= 0 ||
            (this.account.numIncomeSources < this.account.maxIncomeSources &&
                Math.random() < this.account.newIncomeSourceOdds)) {
            this.worldDBManager.findPeerAndUpdate(this.account.peer_cid, this.account.incomeSources, (newPeer) => {
                this.logger.debug(this.account.peer_cid, ' attempting new income source with ', newPeer.peer_cid);
            });
        }
    }
}
exports.default = FindNewIncomeSource;

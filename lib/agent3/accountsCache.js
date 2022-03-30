"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const unifiedLogger_1 = __importDefault(require("./unifiedLogger"));
class AccountCache {
    constructor() {
        this.accountCache = {};
        this.logger = unifiedLogger_1.default.getInstance();
    }
    static getInstance() {
        if (!AccountCache.instance) {
            AccountCache.instance = new AccountCache();
        }
        return AccountCache.instance;
    }
    addAccount(accountData) {
        this.accountCache[accountData.peer_cid] = accountData;
    }
    // Check to see if a peer is in our system, if not add them and then do cb
    containsAccount(targetAccount) {
        let foundAccountData = this.accountCache[targetAccount.peer_cid];
        this.logger.debug('Checking if we have peer:', targetAccount.peer_cid, !!foundAccountData);
        if (foundAccountData) {
            this.logger.debug('Found match for peer', targetAccount.peer_cid, 'in system');
            return true;
        }
        else {
            this.logger.debug('No match found for peer', targetAccount.peer_cid, '. Creating one now.');
            return false;
        }
    }
    getAccountByCID(peer_cid) {
        let foundAccount = this.accountCache[peer_cid];
        if (foundAccount) {
            return foundAccount;
        }
        else {
            console.log('\n\nError in the Account Cache!:\n', this.accountCache);
            throw 'No account with given peer_cid is found ' + peer_cid;
        }
    }
}
exports.default = AccountCache;

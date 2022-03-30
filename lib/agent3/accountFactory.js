"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const baseAccount_1 = __importDefault(require("./accounts/baseAccount"));
class AccountFactory {
    static createAccount(accountType, accountData, host, parameters) {
        var account;
        if (accountType === 'BaseAccount' || accountType == 'default') {
            account = new baseAccount_1.default(accountData, host, parameters);
        }
        // Add more types here...
        else {
            account = new baseAccount_1.default(accountData, host);
        }
        return account;
    }
}
exports.default = AccountFactory;

"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const spendCHIPs_1 = __importDefault(require("./actions/spendCHIPs"));
const findNewSpendingTarget_1 = __importDefault(require("./actions/findNewSpendingTarget"));
const findNewIncomeSource_1 = __importDefault(require("./actions/findNewIncomeSource"));
class ActionFactory {
    static createAction(actionType, account) {
        var action;
        if (actionType === 'NewSpendingSource') {
            action = new findNewSpendingTarget_1.default(account);
        }
        else if (actionType === 'NewIncomeSource') {
            action = new findNewIncomeSource_1.default(account);
        }
        else if (actionType === 'SpendCHIPs') {
            action = new spendCHIPs_1.default(account);
        }
        // Add more types here...
        else {
            throw 'Invalid Action type given.';
        }
        return action;
    }
}
exports.default = ActionFactory;

"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const findNewSpendingTarget_1 = __importDefault(require("./actions/findNewSpendingTarget"));
class ActionFactory {
    static createAction(actionType, agent) {
        var action;
        if (actionType === 'NewSpendingSource') {
            action = new findNewSpendingTarget_1.default(agent);
        }
        // else if (actionType === 'PayVendor') {
        //     action = new PayVendor()
        // }
        // else if (actionType === 'TallyState') {
        //     action = new AcceptTally()
        // }
        // Add more types here...
        else {
            throw "Invalid Action type given.";
        }
        return action;
    }
}
exports.default = ActionFactory;

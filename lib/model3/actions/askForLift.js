"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const sqlmanager_1 = __importDefault(require("../sqlmanager"));
const unifiedLogger_1 = __importDefault(require("../unifiedLogger"));
class AskForLift {
    constructor(account) {
        this.logger = unifiedLogger_1.default.getInstance();
        this.myChipsDBManager = sqlmanager_1.default.getInstance();
        this.account = account;
    }
    run() {
        //TODO: figure out how to get value from individual connections
        let greatestTallyValue = 20; // this is less than the default value, so this will never happen right now...
        if (greatestTallyValue > this.account.diffForLift) {
            this.logger.trace(this.account.peer_cid, 'is asking for a lift!');
            this.myChipsDBManager.requestLift(this.account.peer_cid);
        }
    }
}
exports.default = AskForLift;

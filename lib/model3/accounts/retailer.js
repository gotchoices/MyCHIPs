"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const baseAccount_1 = __importDefault(require("../accounts/baseAccount"));
const actionFactory_1 = __importDefault(require("../actionFactory"));
class Retailer extends baseAccount_1.default {
    constructor(minSale, maxSale, accountData, host, accountParams) {
        super(accountData, host, accountParams);
        this.minSale = minSale;
        this.maxSale = maxSale;
        //TODO these need to have actual parameters for the factory
        this.actions.push(actionFactory_1.default.createAction('FindXClients', this));
    }
}
exports.default = Retailer;

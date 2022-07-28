"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const baseAccount_1 = __importDefault(require("./baseAccount"));
const actionFactory_1 = __importDefault(require("../actionFactory"));
class Employee extends baseAccount_1.default {
    constructor(minSpend, maxSpend, employer, sallary, accountData, host, accountParams) {
        super(accountData, host, accountParams);
        this.minSpend = minSpend;
        this.maxSpend = maxSpend;
        this.employer = employer;
        this.sallary = sallary;
        //TODO these need to have actual parameters for the factory
        this.actions.push(actionFactory_1.default.createAction('FindEmployer', this));
    }
    changeEmployer(employer) {
        this.sallary += this.sallary * 0.1;
        this.employer = employer;
    }
}
exports.default = Employee;

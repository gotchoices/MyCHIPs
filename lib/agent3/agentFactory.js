"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const baseAgent_1 = __importDefault(require("./agents/baseAgent"));
class AgentFactory {
    static createAgent(agentType, agentData, host, parameters) {
        var agent;
        if (agentType === "BaseAgent" || agentType == "default") {
            agent = new baseAgent_1.default(agentData, host, parameters);
        }
        // Add more types here...
        else {
            agent = new baseAgent_1.default(agentData, host);
        }
        return agent;
    }
}
exports.default = AgentFactory;

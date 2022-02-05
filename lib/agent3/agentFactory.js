"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const BaseAgent_1 = __importDefault(require("./agents/BaseAgent"));
class AgentFactory {
    static createAgent(agentType, agentData, parameters) {
        var agent;
        if (agentType === "BaseAgent" || agentType == "default") {
            agent = new BaseAgent_1.default(agentData, parameters);
        }
        // Add more types here...
        else {
            agent = new BaseAgent_1.default(agentData);
        }
        return agent;
    }
}
exports.default = AgentFactory;

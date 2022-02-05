import Agent from './agent'
import BaseAgent from './agents/BaseAgent'

class AgentFactory {
    public static createAgent(agentType: string, agentData: AgentData, parameters?: AdjustableAgentParams) {
        var agent;

        if (agentType === "BaseAgent" || agentType == "default") {
            agent = new BaseAgent(agentData, parameters);
        }
        // Add more types here...
        else {
            agent = new BaseAgent(agentData);
        }

        return agent;
    }
}

export default AgentFactory;
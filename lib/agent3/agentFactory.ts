import Agent from './agent'
import BaseAgent from './agents/baseAgent'

class AgentFactory {
    public static createAgent(agentType: string, agentData: AgentData, host: string, parameters?: AdjustableAgentParams): Agent {
        var agent;

        if (agentType === "BaseAgent" || agentType == "default") {
            agent = new BaseAgent(agentData, host, parameters);
        }
        // Add more types here...
        else {
            agent = new BaseAgent(agentData, host);
        }

        return agent;
    }
}

export default AgentFactory;
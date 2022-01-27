import Agent from './agent'
import BaseAgent from './agents/BaseAgent'

class AgentFactory {
    public static createAgent(agentType: string, agentData: AgentData, parameters: AdjustableSimParams) {
        var agent;

        if (agentType === "BaseAgent") {
            agent = new BaseAgent(agentData, parameters);
        }
        // Add more types here...

        return agent;
    }
}

export default AgentFactory;
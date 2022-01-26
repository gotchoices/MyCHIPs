import Agent from './agent'
import BaseAgent from './agents/BaseAgent'

class AgentFactory {
    public static createAgent(agentType: string) {
        var agent;

        if (agentType === "BaseAgent") {
            agent = new BaseAgent();
        }
        // Add more types here...

        return agent;
    }
}

export default AgentFactory;
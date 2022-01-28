import UnifiedLogger from "./unifiedLogger"

class AgentsCache {
    private static instance: AgentsCache

    private agentCache: {[cid: string]: AgentData}
    private logger: WyclifLogger

    private constructor() {
        this.agentCache = {}
        this.logger = UnifiedLogger.getInstance()
    }

    public static getInstance(): AgentsCache {
        if (!AgentsCache.instance) {
            AgentsCache.instance = new AgentsCache()
        }
        return AgentsCache.instance
    }

    public addAgent(agentData: AgentData) {
        this.agentCache[agentData.peer_cid] = agentData
    }

    // Check to see if a peer is in our system, if not add them and then do cb
    public containsAgent(targetAgent: AgentData): boolean {
        let foundAgentData = this.agentCache[targetAgent.peer_cid]

        this.logger.debug('Checking if we have peer:', targetAgent.peer_cid, !!foundAgentData)
        if (foundAgentData) { 
        this.logger.debug('Found match for peer', targetAgent.peer_cid, 'in system')
        return true
        } 
        else {
        this.logger.debug('No match found for peer', targetAgent.peer_cid, '. Creating one now.')
        return false
        }
    }
}

export default AgentsCache
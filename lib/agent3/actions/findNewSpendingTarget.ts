import Action from "../action";
import Agent from "../agent";
import AgentsCache from "../agentsCache";
import MongoManager from "../mongomanager";
import SQLManager from "../sqlmanager";
import UnifiedLogger from "../unifiedLogger";

class FindNewSpendingSource implements Action{
    logger: WyclifLogger
    myChipsDBManager: SQLManager
    worldDBManager: MongoManager
    agentCache: AgentsCache

    agent: Agent
    
    constructor(agent: Agent) {
        this.logger = UnifiedLogger.getInstance()
        this.myChipsDBManager = SQLManager.getInstance()
        this.worldDBManager = MongoManager.getInstance()
        this.agentCache = AgentsCache.getInstance()

        this.agent = agent
    }

    run(): void {        
        if (this.agent.numSpendingTargets <= 0 ||                 // If the agent has no stocks   or
            (this.agent.numSpendingTargets < this.agent.maxSpendingTargets &&   // (if the agent doesn't have too many stocks and
              Math.random() < this.agent.newSpendingTargetOdds))       //  we randgomly choose to))
        {
            let newPeer: AgentData = this.worldDBManager.findPeerAndUpdate(this.agent.peer_cid, this.agent.spendingTargets)

            this.logger.debug(this.agent.peer_cid, "  attempting new spending source with", newPeer.peer_cid)

            // Save new peer data locally
            if (!this.agentCache.containsAgent(newPeer)) {
                this.myChipsDBManager.addAgent(newPeer)
                this.agentCache.addAgent(newPeer)
            }
            
            // Send new connection request to the potential peer we found
            let newPeerServer = newPeer.peer_socket.split(':')[0]
            this.worldDBManager.insertAction("createAccount", undefined, newPeerServer, () => {
                this.myChipsDBManager.addConnection(this.agent.id, newPeer.id)
                this.agent.numSpendingTargets++
            })
        }
    }
}

export default FindNewSpendingSource;
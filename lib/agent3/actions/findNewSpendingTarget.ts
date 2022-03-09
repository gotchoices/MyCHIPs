import Action from "../action";
import Agent from "../agent";
import AgentsCache from "../agentsCache";
import MongoManager from "../mongomanager";
import SQLManager from "../sqlmanager";
import UnifiedLogger from "../unifiedLogger";

class FindNewSpendingTarget implements Action{
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

	run() {        
		if (this.agent.numSpendingTargets <= 0 ||                 // If the agent has no stocks   or
			(this.agent.numSpendingTargets < this.agent.maxSpendingTargets &&   // (if the agent doesn't have too many stocks and
				Math.random() < this.agent.newSpendingTargetOdds))       //  we randgomly choose to))
		{
			console.log("\n", this.agent.peer_cid, "is finding a new spending target!")
			this.worldDBManager.findPeerAndUpdate(this.agent.peer_cid, this.agent.spendingTargets, (newPeer: AgentData) => {
				console.log(this.agent.peer_cid, "wants to connect to", newPeer.peer_cid)
				console.log("Peer:", newPeer.peer_cid, newPeer.id)

				this.logger.debug(this.agent.peer_cid, "  attempting new spending source with", newPeer.peer_cid)

				// Save new peer data locally
				if (!this.agentCache.containsAgent(newPeer)) {
					this.myChipsDBManager.addAgent(newPeer)
					this.agentCache.addAgent(newPeer)
				}
				
				// See if the peer is on a different server
				let newPeerServer = newPeer.peer_sock.split(':')[0]
				if (newPeerServer != this.agent.host) {
					// If it is, request that the other server gets our info
					this.worldDBManager.insertAction("createAccount", undefined, newPeerServer, this.agent.getAgentData(), () => {
						this.addConnectionRequest(newPeer.id)
					})
				}
				else {
					// Otherwise, just made the connection request
					this.addConnectionRequest(newPeer.id)
				}
			})
		}
	}

	addConnectionRequest(peerID: string) {
		console.log(this.agent.std_name, "sending connection request to", peerID)
		this.myChipsDBManager.addConnectionRequest(this.agent.id, peerID)
		this.agent.numSpendingTargets++
		this.worldDBManager.updateOneAgent(this.agent.getAgentData())
	}
}

export default FindNewSpendingTarget;
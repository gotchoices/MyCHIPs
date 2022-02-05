import Action from "../action";
import Agent from "../agent";
import AgentsCache from "../agentsCache";
import MongoManager from "../mongomanager";
import SQLManager from "../sqlmanager";
import UnifiedLogger from "../unifiedLogger";

class FindNewIncomeSource implements Action {
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
    if (this.agent.numIncomeSources <= 0 || 
      (this.agent.numIncomeSources < this.agent.maxIncomeSources &&
        Math.random() < this.agent.newIncomeSourceOdds))
    {
      let newPeer = this.worldDBManager.findPeerAndUpdate(this.agent.peer_cid, this.agent.incomeSources)

      this.logger.debug(this.agent.peer_cid, " attempting new income source with ", newPeer.peer_cid)

      if (!this.agentCache.containsAgent(newPeer)) {
        this.myChipsDBManager.addAgent(newPeer)
        this.agentCache.addAgent(newPeer)
      }

      let newPeerServer = newPeer.peer_socket.split(':')[0]
      this.worldDBManager.insertAction("createAccount", undefined, newPeerServer, () => {
        this.myChipsDBManager.addConnectionRequest(this.agent.id, newPeer.id)
        // TODO: This stuff should only be done when the connection is accepted by the peer. Right now the peers always accept requests, so we can do it here. I'm not sure how we will get notified when the connection is accepted...
        this.agent.numIncomeSources++
        this.worldDBManager.updateOneAgent(this.agent)
      })
    }
  }

}

export default FindNewIncomeSource
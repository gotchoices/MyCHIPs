import Action from "../action";
import Agent from "../agent";
import AgentsCache from "../agentsCache";
import MongoManager from "../mongomanager";
import SQLManager from "../sqlmanager";
import UnifiedLogger from "../unifiedLogger";

class SpendCHIPs implements Action {
    logger: WyclifLogger;
    myChipsDBManager: SQLManager;
    worldDBManager: MongoManager;
    agentCache: AgentsCache;

    agent: Agent;
    
    constructor(agent: Agent) {
        this.logger = UnifiedLogger.getInstance()
        this.myChipsDBManager = SQLManager.getInstance()
        this.worldDBManager = MongoManager.getInstance()
        this.agentCache = AgentsCache.getInstance()

        this.agent = agent
    }
    

    run(): void {
        if (this.agent.numSpendingTargets > 0 && this.agent.netWorth > this.agent.minWorthToSpend) {
            let chipsToSpend = Math.floor(Math.random() * Math.max(this.agent.netWorth * this.agent.maxToSpend, 1000))

            let peerToPayID = this.agent.spendingTargets[Math.floor(Math.random() * this.agent.numSpendingTargets)]
            let peerToPay = this.agentCache.getAgent(peerToPayID)

            let sequence: number = this.agent.foil_seqs[peerToPayID]

            this.myChipsDBManager.addPayment(this.agent.id, peerToPay.id, chipsToSpend, sequence)
        }
    }

}

export default SpendCHIPs;
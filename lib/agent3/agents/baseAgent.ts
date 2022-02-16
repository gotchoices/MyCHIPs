// import { WyclifLogger } from '../../@types/global'
import Action from '../action';
import Agent from '../agent';
import MongoManager from '../mongomanager';
import SQLManager from '../sqlmanager';
import ActionFactory from '../actionFactory';
import UnifiedLogger from '../unifiedLogger';

class BaseAgent implements Agent {
    id: number;
    std_name: string;
    peer_cid: any;
    host: string;
    numSpendingTargets: number;
    numIncomeSources: number;
    foil_seq: number[];
    netWorth: number;
    hosted_ent: boolean;
    actions: Action[];
    lastActionTaken: string;
    spendingTargets: string[];
    incomeSources: string[];
    seqs: any[];
    types: any[];
    
    newIncomeSourceOdds: number 
    adjustSettingsOdds: number 
    newSpendingTargetOdds: number
    maxSpendingTargets: number
    maxIncomeSources: number
    minWorthToSpend: number
    maxToSpend: number;

    worldDBManager: MongoManager;
    myChipsDBManager: SQLManager;
    logger: WyclifLogger;

    constructor(agentData: AgentData, host: string, agentParams?: AdjustableAgentParams) {
        this.worldDBManager = MongoManager.getInstance();
        this.myChipsDBManager = SQLManager.getInstance();
        this.logger = UnifiedLogger.getInstance();

        //TODO these need to have actual parameters for the factory
        this.actions = [];
        this.actions.push(ActionFactory.createAction('NewSpendingSource', this));
        // this.actions.push(ActionFactory.createAction('NewIncomeSource', this)); // Not correctly implemented yet 
        this.actions.push(ActionFactory.createAction('SpendCHIPs', this));

        //TODO: finish applying this info from agent data and params
        this.id = agentData.id;
        this.std_name = agentData.std_name;
        this.peer_cid = agentData.peer_cid;
        this.host = host
        this.numSpendingTargets = 0;
        this.numIncomeSources = 0;
        this.foil_seq = agentData.foil_seqs;
        this.netWorth = 0;

        this.hosted_ent = true;
        this.lastActionTaken = '';
        this.spendingTargets = [];
        this.incomeSources = [];
        this.seqs = [];
        this.types = [];

        this.newIncomeSourceOdds = agentParams?.newIncomeSourceOdds || 0.1
        this.adjustSettingsOdds = agentParams?.adjustSettingsOdds || 0.5
        this.newSpendingTargetOdds = agentParams?.newSpendingTargetOdds || 0.15 
        this.maxSpendingTargets = agentParams?.maxSpendingTargets || 2
        this.maxIncomeSources = agentParams?.maxIncomeSources || 3
        this.minWorthToSpend = agentParams?.minWorthToSpend || -10000
        this.maxToSpend = agentParams?.maxToSpend || 0.1
    }
    
    takeAction(): void {
        // For now, I'm just having the Agent perform all of its Actions. Since there's a percentage
        // associated with each Action that determines how likely it is to actually happen, I think
        // this is ok.
        this.actions.forEach((action) => {
            action.run()
        })
    }

    acceptNewConnection(message: any) {
        // I don't know how to tell the difference between types of connections (whether this account is the income source or spending target)
        // As a default Account, we will always accept a connection
        this.myChipsDBManager.updateConnectionRequest(message.entity, message.sequence, true)

        // TODO: update data here (depends on what kind of connection it is though...)
    }
}

export default BaseAgent;
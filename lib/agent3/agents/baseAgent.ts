// import { WyclifLogger } from '../../@types/global'
import Action from '../action';
import Agent from '../agent';
import MongoManager from '../mongomanager';
import SQLManager from '../sqlmanager';
import ActionFactory from '../actionFactory';
import UnifiedLogger from '../unifiedLogger';

class BaseAgent implements Agent {
	id: string;
	std_name: string;
	ent_name: string;
	first_name: string;
	peer_cid: any;
	birthday: string;
	host: string;
	entity_type: string;
	peer_socket: string;
	random: number;
	numSpendingTargets: number;
	numIncomeSources: number;
	foil_seqs: number[];
	netWorth: number;
	hosted_ent: boolean;
	actions: Action[];
	lastActionTaken: string;
	spendingTargets: string[];
	incomeSources: string[];
	stock_seqs: any[];
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
		console.log("Creating account object for", agentData.std_name)
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
		this.ent_name = agentData.ent_name;
		this.first_name = agentData.fir_name;
		this.peer_cid = agentData.peer_cid;
		this.peer_socket = agentData.peer_sock;
		this.host = host
		this.entity_type = agentData.ent_type || "Default person"
		this.birthday = agentData.born_date || "yesterday"
		this.random = Math.random()

		this.numSpendingTargets = 0;
		this.numIncomeSources = 0;
		this.foil_seqs = agentData.foil_seqs || [];
		this.stock_seqs = agentData.stock_seqs || [];
		this.netWorth = 0;

		this.hosted_ent = true;
		this.lastActionTaken = '';
		this.spendingTargets = [];
		this.incomeSources = [];
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
		console.log(this.peer_cid, "is accepting a connection request!")
		this.myChipsDBManager.updateConnectionRequest(message.entity, message.sequence, true)

		// TODO: update data here (depends on what kind of connection it is though...)
	}

	getAgentData(): AgentData {
		return {
			id: this.id,
			std_name: this.std_name,
			ent_name: this.ent_name,
			fir_name: this.first_name,
			ent_type: this.entity_type,
			user_ent: this.id,		// Idk why these are equivalent, but they are in agent2...
			peer_cid: this.peer_cid,
			peer_sock: this.peer_socket,
			born_date: this.birthday,
			stocks: this.numSpendingTargets,
			foils: this.numIncomeSources,
			partners: [...this.spendingTargets, ...this.incomeSources],
			vendors: this.spendingTargets,
			clients: this.incomeSources,
			stock_seqs: this.stock_seqs,
			foil_seqs: this.foil_seqs,
			units: this.netWorth,
			seqs: [...this.stock_seqs, ...this.foil_seqs],
			random: this.random,
			host: this.host
		}
	}
}

export default BaseAgent;
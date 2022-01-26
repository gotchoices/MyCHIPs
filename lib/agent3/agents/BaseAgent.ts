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
    stocks: number;
    foils: number;
    foil_seq: any;
    units: any;
    maxToPay: number;
    maxTargets: number;
    user_ent: boolean;
    actions: Action[];
    lastActionTaken: string;
    targets: any[];
    seqs: any[];
    types: any[];
    worldDBManager: MongoManager;
    myChipsDBManager: SQLManager;
    //TODO for some reason this is not importing automatically from the global.d.ts
    logger: WyclifLogger;

    constructor() {
        this.worldDBManager = MongoManager.getInstance();
        this.myChipsDBManager = SQLManager.getInstance();
        this.logger = UnifiedLogger.getInstance();

        //TODO these need to have actual parameters for the factory
        this.actions = [];
        this.actions.push(ActionFactory.createAction('NewTally', this, null, null, null));
        this.actions.push(ActionFactory.createAction('PayVendor', this, null, null, null));
        this.actions.push(ActionFactory.createAction('TallyState', this, null, null, null));

        //TODO set these with parameter values from the config
        this.id = 0;
        this.std_name = '';
        this.peer_cid = '';
        this.stocks = 0;
        this.foils = 0;
        this.foil_seq = '';
        this.units = '';
        this.maxToPay = 0;
        this.maxTargets = 0;
        this.user_ent = true;
        this.lastActionTaken = '';
        this.targets = [];
        this.seqs = [];
        this.types = [];

    }
    
    takeAction(): void {
        //generate a random number between 1 and 100
        let rand: number = Math.floor(Math.random() * 101);
        
        //do actions based on a switch here?
        //We may need to create an enum that has all of the actions in it or something 
    }
    
    //TODO this may need to be moved somewhere else.
    checkSettings(): void {
        let sqls: string[] = [],
        i = 0
        
        this.targets.forEach((t: any) => {
            let seq = this.seqs[i],
            ent = this.id,
            newTarg = Math.random() * this.maxTargets,
            newBound = Math.random() * newTarg * 0.5 + newTarg,
            reward = (Math.random() * 5) / 100 + 0.05
            // this.logger.trace('   seq:', seq, 'type:', this.types[i])
            if (this.types[i] == 'foil') {
                //For now, we will assert settings only on foil tallies
                sqls.push(`insert into mychips.tally_sets (tset_ent, tset_seq, target, bound, reward, signature) values ('${ent}', ${seq}, ${newTarg}, ${newBound}, ${reward}, 'Valid')`)
            }
        
            i++
        })
            // this.logger.debug('  Settings:', sqls.join(';'))
        this.myChipsDBManager.query(sqls.join(';'), null, (e, r) => {
            if (e) {
                // this.logger.error('In settings:', e.stack)
                return
            }
        })
    }
}

export default BaseAgent;
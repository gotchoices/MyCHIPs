import Agent from './agent'
import AcceptTally from './actions/acceptTally'
import PayVendor from './actions/payVendor'
import Action from './action';
import FindNewSpendingSource from './actions/findNewSpendingTarget';

class ActionFactory {
    public static createAction(actionType: string, agent: Agent) {
        var action: Action;
    
        if (actionType === 'NewSpendingSource') {
            action = new FindNewSpendingSource(agent)
        }
        // else if (actionType === 'PayVendor') {
        //     action = new PayVendor()
        // }
        // else if (actionType === 'TallyState') {
        //     action = new AcceptTally()
        // }
        // Add more types here...
        else {
            throw "Invalid Action type given."
        }
    
        return action;
    }
}

export default ActionFactory;
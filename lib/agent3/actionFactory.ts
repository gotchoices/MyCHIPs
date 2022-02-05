import Agent from './agent'
import SpendCHIPs from './actions/spendCHIPs'
import Action from './action';
import FindNewSpendingTarget from './actions/findNewSpendingTarget';

class ActionFactory {
    public static createAction(actionType: string, agent: Agent) {
        var action: Action;
    
        if (actionType === 'NewSpendingSource') {
            action = new FindNewSpendingTarget(agent)
        }
        else if (actionType === 'SpendCHIPs') {
            action = new SpendCHIPs(agent)
        }
        // Add more types here...
        else {
            throw "Invalid Action type given."
        }
    
        return action;
    }
}

export default ActionFactory;
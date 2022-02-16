import Agent from './agent'
import SpendCHIPs from './actions/spendCHIPs'
import Action from './action';
import FindNewSpendingTarget from './actions/findNewSpendingTarget';
import FindNewIncomeSource from './actions/findNewIncomeSource';

class ActionFactory {
    public static createAction(actionType: string, agent: Agent) {
        var action: Action;
    
        if (actionType === 'NewSpendingSource') {
            action = new FindNewSpendingTarget(agent)
        }
        else if (actionType === 'NewIncomeSource') {
            action = new FindNewIncomeSource(agent)
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
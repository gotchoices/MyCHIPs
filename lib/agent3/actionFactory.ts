import Agent from './agent'
import NewTally from './actions/newTally'
import TallyState from './actions/tallyState'
import PayVendor from './actions/payVendor'

class ActionFactory {
    public static createAction(actionType: string, agent: Agent, parameters, checkForPeer, remoteCall) {
        var action;
    
        if (actionType === 'NewTally') {
            action = new NewTally(agent, parameters, checkForPeer, remoteCall)
        }
        if (actionType === 'PayVendor') {
            action = new PayVendor(agent, parameters, checkForPeer, remoteCall)
        }
        if (actionType === 'TallyState') {
            action = new TallyState(agent, parameters, checkForPeer, remoteCall)
        }
        // Add more types here...
    
        return action;
    }
}

export default ActionFactory;
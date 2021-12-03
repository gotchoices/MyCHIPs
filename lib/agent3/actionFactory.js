import actions from "./actions.js";

export default {
  createAction(type, agentData, parameters, worldDBManager, myChipsDBManager,
    checkForPeer, remoteCall, getAgentInfo, logger) {
    var action;
  
    if (type === "makeNewTally") {
      action = new actions.MakeNewTally(agentData, parameters, worldDBManager, myChipsDBManager,
        checkForPeer, remoteCall, logger);
    }
    else if (type == "payVendor") {
      action = new actions.PayVendor(agentData, parameters, myChipsDBManager, getAgentInfo, logger);
    }
    // Add more types here...
    return action;
  }, 
  
  createStandardActions(agentData, parameters, worldDBManager, myChipsDBManager, checkForPeer,
    remoteCall, getAgentInfo, logger) {
    var actions = [];
  
    actions.push(new actions.MakeNewTally(agentData, parameters, worldDBManager, myChipsDBManager,
      checkForPeer, remoteCall, logger));
    actions.push(new actions.PayVendor(agentData, parameters, myChipsDBManager, getAgentInfo, logger));
    // Add more standard types here...
    return actions;
  }
} 

'use strict'
const actions = require('./actions.js').default
module.exports = {
  createAction(
    type,
    agentData,
    parameters,
    worldDBFacade,
    myChipsDBFacade,
    checkForPeer,
    remoteCall,
    logger
  ) {
    var action
    if (type === 'makeNewTally') {
      action = actions.MakeNewTally(
        agentData,
        parameters,
        worldDBFacade,
        myChipsDBFacade,
        checkForPeer,
        remoteCall,
        logger
      )
    }
    // Add more types here...
    return action
  },
}

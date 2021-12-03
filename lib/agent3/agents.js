import actionFactory from "./actionFactory";

class DefaultAgent {

}

class Consumer {
  #actions
  #params

  constructor(parameters, worldDBManager, myChipsDBManager, checkForPeer, remoteCall, getAgentInfo, logger) {
    this.#params.addClient = parameters.addClient
    this.#params.addVendor = parameters.addVendor
    ...

    this.#actions = actionFactory.createStandardActions(TODO)
  }
}

// Export Agents
export default {
  Consumer,
  DefaultAgent
};
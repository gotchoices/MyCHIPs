module.exports = class AgentCluster {
  #params

  constructor() {
    this.#params = new Map()
    this.run()
  }

  // calls run on all of the agents
  run() {}

  // gets the params from the SQLManager
  eatParams() {}

  // gets agents from SQL and puts hosted agent info into MongoDB
  eatAgents() {}

  notifyOfParamsChange() {}

  notifyOfAgentsChange() {}

  notifyOfTallyChange() {}

  notifyOfAction() {}
}

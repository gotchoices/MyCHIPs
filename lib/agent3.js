module.exports = class AgentCluster {
  #params

  constructor() {
    this.loadParamsConfig()
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

  loadParamsConfig() {
    const fs = require('fs')
    const yaml = require('js-yaml')

    try {
      let fileContents = fs.readFileSync('./agent3/paramConfig.yaml', 'utf8')
      this.#params = yaml.safeLoad(fileContents)

      console.log(data)
    } catch (e) {
      console.log(e)
    }
  }
}

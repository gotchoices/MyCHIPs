module.exports = class SQLManager {
  #channels = []
  #sqlConfig
  #host
  #database
  #user
  #port

  constructor(sqlConfig) {
    this.#sqlConfig = sqlConfig
  }

  updateParameters() {}

  updateAgents() {}

  updateTally() {}

  getParams() {}

  getAgents() {}

  #query() {}
}

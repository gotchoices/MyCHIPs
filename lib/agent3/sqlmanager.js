module.exports = class SQLManager {
  #channels = []
  #sqlConfig
  #host
  #database
  #user
  #port

  constructor(sqlConfig, logger) {
    // Add fields to config
    this.#sqlConfig = Object.assign(
      {
        log: logger,
        listen: ['parm_agent', 'mychips_admin', 'mychips_user'],
      },
      sqlConfig
    )
  }

  updateParameters() {}

  updateAgents() {}

  updateTally() {}

  getParams() {}

  getAgents() {}

  #query() {}
}

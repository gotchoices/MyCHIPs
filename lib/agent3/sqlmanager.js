const { dbClient } = require('wyseman')

module.exports = class SQLManager {
  #channels = []
  #config
  #logger
  #host
  #database
  #user
  #port
  #dbConnection

  constructor(sqlConfig, logger) {
    this.#logger = logger

    // Add fields to config
    this.#config = Object.assign(
      {
        log: this.#logger,
        listen: ['parm_agent', 'mychips_admin', 'mychips_user'],
      },
      sqlConfig
    )
  }

  createConnection(
    params,
    notifyOfAgentChange,
    notifyOfParamsChange,
    notifyOfTallyChange
  ) {
    this.#dbConnection = new dbClient(this.#config, (channel, payload) => {
      //Initialize Database connection
      let msg
      this.#logger.trace('Agent DB async on:', channel, 'payload:', payload)
      if (payload)
        try {
          msg = JSON.parse(payload)
        } catch (e) {
          log.error('Parsing json payload: ' + payload)
        }
      if (channel == 'parm_agent') {
        //Parameter updated
        this.log.debug('Parameter', msg.target, '=', msg.value, msg)
        if (msg.target in params && msg.value)
          notifyOfParamsChange(msg.target, msg.value)
      } else if (channel == 'mychips_admin') {
        //Something in the user data has changed
        if (msg.target == 'peers' || msg.target == 'tallies') {
          notifyOfAgentChange(msg)
        }
      } else if (channel == 'mychips_user') {
        //Respond as a real user would to a request/event
        if (msg.target == 'tally') notifyOfTallyChange(msg)
      }
    })
  }

  isActiveQuery() {
    return this.#dbConnection.client.activeQuery != null
  }

  closeConnection() {
    this.#dbConnection.disconnect()
  }

  updateParameters() {}

  updateAgents() {}

  updateTally() {}

  getParams() {}

  getAgents() {}

  query(...args) {
    this.#dbConnection.query(...args)
  }
}

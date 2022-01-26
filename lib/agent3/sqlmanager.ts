// const { dbClient } = require('wyseman')
import { dbClient } from 'wyseman'
import UnifiedLogger from './unifiedLogger'

const userSql = `select id, std_name, ent_name, fir_name, ent_type, user_ent,
	peer_cid, peer_sock, stocks, foils, partners, vendors, clients,
	vendor_cids, client_cids, stock_seqs, foil_seqs, units, types, seqs, targets
	from mychips.users_v_tallysum
	where not peer_ent isnull`
const peerSql = `insert into mychips.peers_v 
	(ent_name, fir_name, ent_type, born_date, peer_cid, peer_host, peer_port) 
	values ($1, $2, $3, $4, $5, $6, $7) returning *`

interface Config extends DBConfig {
  log: WyclifLogger
  listen: string[]
}

class SQLManager {
  private static singletonInstance: SQLManager
  private config: Config
  private logger: WyclifLogger
  private dbConnection: dbClient
  private params: AdjustableSimParams
  // These member variables are never used, but might be if we implement some of the other functions
  // private channels: string[] = []
  // private host: string 
  // private database: string
  // private user: string
  // private port: string

  private constructor(sqlConfig: DBConfig, params: AdjustableSimParams) {
    this.logger = UnifiedLogger.getInstance()
    this.params = params

    // Add fields to config
    this.config = Object.assign(
      {
        log: this.logger,
        listen: ['parm_agent', 'mychips_admin', 'mychips_user'],
      },
      sqlConfig
    )
  }

  public static getInstance(sqlConfig?: DBConfig, params?: AdjustableSimParams): SQLManager {
    if (!SQLManager.singletonInstance && sqlConfig && params) {
      SQLManager.singletonInstance = new SQLManager(sqlConfig, params)
    }
    else if (!SQLManager && (!sqlConfig || !params)) {
      throw new Error('no singleton instance exists and no paramaters supplied for creation')
    }

    return SQLManager.singletonInstance
  }

  createConnection(
    notifyOfAgentChange: (msg: any) => void,
    notifyOfParamsChange: (target: string, value: any) => void,
    notifyOfTallyChange: (msg: any) => void
  ) {
    this.dbConnection = new dbClient(this.config, (channel, payload) => {
      //Initialize Database connection
      let msg: any
      this.logger.trace('Agent DB async on:', channel, 'payload:', payload)
      if (payload)
        try {
          msg = JSON.parse(payload)
        } catch (e) {
          this.logger.error('Parsing json payload: ' + payload)
        }
      if (channel == 'parm_agent') {
        //Parameter updated
        this.logger.debug('Parameter', msg.target, '=', msg.value, msg)
        if (msg.target in this.params && msg.value)
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
    this.logger.info('SQL Connection Created')
  }

  isActiveQuery() {
    return this.dbConnection.client.activeQuery != null
  }

  closeConnection() {
    this.dbConnection.disconnect()
  }

  updateParameters() {}

  updateAgents() {}

  updateTally() {}

  getParams() {}

  getAgents() {}

  queryUsers(callback: (e: any, r: any)=>any) {
    this.query(userSql, callback)
  }

  queryLatestUsers(time: string, callback: (err: any, res: any)=>any) {
    this.query(userSql + ' and latest >= $1', [time], callback)
  }

  queryPeers(callback: (err: any, res: any)=>any) {
    this.query(peerSql, callback)
  }

  query(...args: any[]) {
    this.dbConnection.query(...args)
  }
}

export default SQLManager

// const { dbClient } = require('wyseman')
import { dbClient } from 'wyseman'
import UnifiedLogger from './unifiedLogger'

import { v4 as uuidv4 } from 'uuid'
import { Lift } from '../@types/models'

const userSql = `select id, std_name, ent_name, fir_name, ent_type, user_ent,
	peer_cid, peer_agent, peer_host, peer_port, mychips.user_cert(id) as cert, stocks, foils, part_cids, vendors, clients,
	vendor_cids, vendor_agents, client_cids, stock_seqs, foil_seqs, net, types, seqs, targets
	from mychips.users_v_tallysum
	where not user_ent isnull`
const parmQuery = "select parm,value from base.parm_v where module = 'agent'"

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
  /** Used to make sure that users are only loaded once */
  private loadingUsers: boolean = false

  private constructor(sqlConfig: DBConfig, params: AdjustableSimParams) {
    this.logger = UnifiedLogger.getInstance()
    this.params = params

    // Add fields to config
    this.config = Object.assign(
      {
        log: this.logger,
        listen: ['parm_model', 'mychips_admin', 'mychips_user'],
      },
      sqlConfig
    )
  }

  public static getInstance(
    sqlConfig?: DBConfig,
    params?: AdjustableSimParams
  ): SQLManager {
    if (!SQLManager.singletonInstance && sqlConfig && params) {
      SQLManager.singletonInstance = new SQLManager(sqlConfig, params)
    } else if (!SQLManager && (!sqlConfig || !params)) {
      throw new Error(
        'no singleton instance exists and no paramaters supplied for creation'
      )
    }

    return SQLManager.singletonInstance
  }

  createConnection(
    notifyOfAccountChange: (msg: any) => void,
    notifyOfParamsChange: (target: string, value: any) => void,
    notifyOfTallyChange: (msg: any) => void
  ) {
    this.logger.trace('Connecting to MyCHIPs DB...')
    this.dbConnection = new dbClient(this.config, (channel, payload) => {
      //Initialize Database connection
      let msg: any
      this.logger.trace('Account DB async on:', channel, 'payload:', payload)
      if (payload)
        try {
          msg = JSON.parse(payload)
        } catch (e) {
          this.logger.error('Parsing json payload: ' + payload)
        }
      if (channel == 'parm_model') {
        //Parameter updated
        this.logger.debug('Parameter', msg.target, '=', msg.value, msg)
        if (msg.target in this.params && msg.value)
          notifyOfParamsChange(msg.target, msg.value)
      } else if (channel == 'mychips_admin') {
        //Something in the user data has changed
        if (msg.target == 'peers' || msg.target == 'tallies') {
          notifyOfAccountChange(msg)
        }
      } else if (channel == 'mychips_user') {
        //Another account is contacting us
        if (msg.target == 'tally') {
          //Someone wants to make a tally with one of our accounts
          notifyOfTallyChange(msg)
        }
      }
    })
    this.logger.trace('SQL Connection Created')
  }

  addConnectionRequest(
    requestingAccountID: string,
    requestingAccountCertificate: certificate,
    targetAccountCertificate: certificate
  ) {
    let uuid = uuidv4()
    let sig = 'Valid'
    let contract = { name: 'mychips-0.99' }

    this.logger.debug(
      'Tally request:',
      requestingAccountID,
      targetAccountCertificate
    )
    this.logger.debug(
      'Making tally between',
      requestingAccountCertificate.chad.cid,
      'and',
      targetAccountCertificate.chad.cid
    )

    this.query(
      'insert into mychips.tallies_v (tally_ent, tally_uuid, contract, request, hold_cert, part_cert, hold_sig, tally_type) values ($1, $2, $3, $4, $5, $6, $7, $8);',
      [
        requestingAccountID,
        uuid,
        contract,
        'offer',
        requestingAccountCertificate,
        targetAccountCertificate,
        sig,
        'foil',
      ],
      (err, res) => {
        if (err) {
          this.logger.error('Inserting a tally:', err.stack)
          console.error(err)
          return
        }
        this.logger.debug(
          '  Initial tally by:',
          requestingAccountID,
          ' with partner:',
          targetAccountCertificate
        )
      }
    )
  }

  updateConnectionRequest(entity, sequence, accepted: boolean) {
    if (accepted) {
      let target = 1
      this.query(
        "update mychips.tallies set request = 'open', hold_sig = $3, target = $4 where tally_ent = $1 and tally_seq = $2 returning request, status;",
        [entity, sequence, 'Accepted', target],
        (err, res) => {
          if (err) {
            this.logger.error('Updating a Tally:', err.stack)
            console.error('Error trying to accept tally for', entity, sequence)
          }
          let row = res.rows && res.rows.length >= 1 ? res.rows[0] : null
          this.logger.debug(
            'Tally accepted:',
            row.tally_ent,
            row.tally_seq,
            row.request,
            row.status
          )
        }
      )
    } else {
      //TODO: figure out how to mark the tally as unaccepted (just delete it?)
    }
  }

  addPayment(spenderId, receiverId, chipsToSpend: number, sequence: number) {
    let quid = 'Inv' + Math.floor(Math.random() * 1000)

    this.logger.verbose(
      '  payVendor:',
      spenderId,
      '->',
      receiverId,
      'on:',
      sequence,
      'Units:',
      chipsToSpend
    )

    this.query(
      'insert into mychips.chits_v (chit_ent,chit_seq,chit_uuid,signature,units,memo,request) values ($1,$2,$3,$4,$5,$6,$7)',
      [spenderId, sequence, uuidv4(), 'Signed', chipsToSpend, quid, 'good'],
      (e, r) => {
        if (e) {
          this.logger.error('In payment:', e.stack)
          return
        }
        this.logger.debug('  payment:', spenderId, 'to:', receiverId)
      }
    )
  }

  isActiveQuery() {
    return this.dbConnection.client.activeQuery != null
  }

  closeConnection() {
    this.dbConnection.disconnect()
  }

  /**
   * Gets parameters from the MyCHIPS DB. May not be needed with new paramConfig.yaml
   * @param callback Function to call once the query is finished
   */
  getParameters(callback: (parameters: ParamData[]) => void) {
    this.query(parmQuery, (err, res) => {
      if (err) {
        this.logger.error('Getting parameters:', err.stack)
        return
      }
      callback(res.rows)
    })
  }

  /**
   * Executes database query to get all initial acounts
   * @param callback: eatAccounts - loads queried accounts into the worldDB
   * */
  // ! TODO Does this fetch from all peers?
  // ! ANSWER No, just from the matching pg database/container
  queryAccounts(callback: (agents: AccountData[], first: boolean) => any) {
    this.logger.debug('Getting users from MyCHIPs DB')
    this.query(userSql, (err: any, res: any) => {
      if (err) {
        this.logger.error('Getting Users:', err.stack)
        return
      }
      this.logger.trace('Loaded accounts:', res.rows.length)
      callback(res.rows, true)
    })
  }

  queryLatestUsers(time: string, callback: (accounts: AccountData[]) => any) {
    // Only load users one at time
    // if (!this.loadingUsers) {
    //   this.loadingUsers = true
    this.query(userSql + ' and latest >= $1', [time], (err: any, res: any) => {
      this.loadingUsers = false
      if (err) {
        this.logger.error('Getting latest Users:', err.stack)
        return
      }
      this.logger.trace('Loaded accounts:', res.rows.length)
      callback(res.rows)
    })
    // } else {
    //   console.log("Tried to query users when I'm already doing that!")
    // }
  }

  /** Starts a lift starting from a given peer. I don't know what it means to have a bottom or end peer though... */
  requestLift(start_peer_cid: string, end_peer_cid?: string): void {
    this.dbConnection.query(
      'select mychips.lift_circuit($1, $2)',
      [start_peer_cid, end_peer_cid],
      (err, result) => {
        if (err) {
          this.logger.error("Can't start a lift:", err)
        } else {
          this.logger.debug('We did a lift!\n', result)
        }
      }
    )
  }

  /** Searches for lifts on this server and performs them */
  performAutoLifts(): Lift | void {
    this.logger.debug('Running automatic lifts!\n')
    this.dbConnection.query('select mychips.lift_cycle(100)', (err, result) => {
      if (err) {
        this.logger.error('Automatic lifts:', err)
      } else {
        this.logger.debug('Results from auto lifts:\n', result)
        return result.row[0]
      }
    })
  }

  /** Maybe this can run at the end */
  getLiftData(): LiftAnalytics | void {
    this.dbConnection.query(
      'select lift_guid,lift_seq,request,status,units,circular,path,dest_chid,dest_host,signature from mychips.lifts_v',
      (err, res) => {
        if (err) {
          this.logger.error('Error while getting lift analytics')
          return null
        } else {
          return res
        }
      }
    )
  }

  query(...args: any[]) {
    this.dbConnection.query(...args)
  }
}

export default SQLManager

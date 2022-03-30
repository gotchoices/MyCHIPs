// const { dbClient } = require('wyseman')
import { dbClient } from 'wyseman'
import UnifiedLogger from './unifiedLogger'

import uuidv4 from 'uuid/v4'

const userSql = `select id, std_name, ent_name, fir_name, ent_type, user_ent,
	peer_cid, peer_sock, stocks, foils, partners, vendors, clients,
	vendor_cids, client_cids, stock_seqs, foil_seqs, units, types, seqs, targets
	from mychips.users_v_tallysum
	where not peer_ent isnull`
const peerSql = `insert into mychips.peers_v 
	(ent_name, fir_name, ent_type, born_date, peer_cid, peer_host, peer_port) 
	values ($1, $2, $3, $4, $5, $6, $7) returning *`
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
    console.log('Connecting to MyCHIPs DB...')
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
      if (channel == 'parm_agent') {
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
        //Respond as a real user would to a request/event
        if (msg.target == 'tally') notifyOfTallyChange(msg)
      }
    })
    console.log('MyCHIPs DB Connected!')
    this.logger.info('SQL Connection Created')
  }

  addPeerAccount(
    accountData: AccountData,
    callback?: (newGuy: AccountData) => void
  ) {
    console.log('Adding', accountData.peer_cid, 'to local DB')
    this.dbConnection.query(
      peerSql,
      [
        accountData.ent_name,
        accountData.fir_name,
        accountData.ent_type,
        accountData.born_date,
        accountData.peer_cid,
        accountData.peer_host || accountData.peer_sock.split(':')[0]!,
        accountData.peer_port || accountData.peer_sock.split(':')[1]!,
      ],
      (err, res) => {
        if (err) {
          this.logger.error('Adding peer:', accountData.peer_cid, err.stack)
          return
        }
        let newGuy = res.rows[0]
        this.logger.debug(
          '  Inserting partner locally:',
          newGuy.std_name,
          newGuy.peer_socket
        )
        console.log('Added', newGuy.peer_cid, 'to local DB')
        if (callback) callback(newGuy)
      }
    )
  }

  addConnectionRequest(requestingAccountID: string, targetAccountID: string) {
    let guid = uuidv4()
    let sig = 'Valid'
    let contract = { name: 'mychips-0.99' }

    this.logger.debug('Tally request:', requestingAccountID, targetAccountID)
    console.log(
      'Making a connection/tally between',
      requestingAccountID,
      'and',
      targetAccountID
    )

    this.query(
      'insert into mychips.tallies_v (tally_ent, tally_guid, partner, user_sig, contract, request) values ($1, $2, $3, $4, $5, $6);',
      [requestingAccountID, guid, targetAccountID, sig, contract, 'draft'],
      (err, res) => {
        if (err) {
          this.logger.error('Inserting a tally:', err.stack)
          console.log(
            'Error while making tally between',
            requestingAccountID,
            'and',
            targetAccountID
          )
          console.log(err)
          return
        }
        this.logger.debug(
          '  Initial tally by:',
          requestingAccountID,
          ' with partner:',
          targetAccountID
        )
      }
    )
  }

  updateConnectionRequest(entity, sequence, accepted: boolean) {
    if (accepted) {
      this.query(
        "update mychips.tallies_v set request = 'open' where tally_ent = $1 and tally_seq = $2",
        [entity, sequence],
        (err, res) => {
          if (err) {
            this.logger.error('Updating a Tally:', err.stack)
          }
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
      "insert into mychips.chits_v (chit_ent,chit_seq,chit_guid,chit_type,signature,units,quidpro,request) values ($1,$2,$3,'tran',$4,$5,$6,$7)",
      [spenderId, sequence, uuidv4(), 'Valid', chipsToSpend, quid, 'userDraft'],
      (e, r) => {
        if (e) {
          this.logger.error('In payment:', e.stack)
          console.log(
            'Error when',
            spenderId,
            'tried to pay',
            receiverId,
            chipsToSpend,
            'chips'
          )
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
  queryUsers(callback: (agents: AccountData[], all: boolean) => any) {
    console.log('Getting users from MyCHIPs DB')
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
    this.query(userSql + ' and latest >= $1', [time], (err: any, res: any) => {
      if (err) {
        this.logger.error('Getting latest Users:', err.stack)
        return
      }
      this.logger.trace('Loaded accounts:', res.rows.length)
      callback(res.rows)
    })
  }

  queryPeers(callback: (err: any, res: any) => any) {
    this.query(peerSql, callback)
  }

  query(...args: any[]) {
    this.dbConnection.query(...args)
  }
}

export default SQLManager

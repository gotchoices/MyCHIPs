import { MongoClient, Db, Collection, Document } from 'mongodb'
import Os from 'os'
import UnifiedLogger from './unifiedLogger'
import { Lift, Server } from '../@types/models'
import WorldManagerInterface from './worldManagerInterface'

class MongoManager implements WorldManagerInterface {
  private static singletonInstance: MongoManager
  private docConfig: DBConfig
  private host: string
  private logger: WyclifLogger
  private dbConnection!: Db

  private mongoClient!: MongoClient
  private accountsCollection!: Collection<Document> //TODO: Change this
  private analyticsLiftCollection!: Collection<Document>
  private analyticsServerCollection!: Collection<Document>

  /** A cache in which to store callbacks that need to run when actions sent to foreign servers are completed */
  private foreignActionCallbackCache!: { [x: string]: (...args: any[]) => any }
  private foreignActionTagIndex!: number

  private constructor(dbConfig: DBConfig, argv) {
    this.docConfig = dbConfig
    this.logger = UnifiedLogger.getInstance()

    // MongoDB host name
    this.host = argv.peerServer || Os.hostname()

    this.foreignActionTagIndex = 0
    this.foreignActionCallbackCache = {}
  }

  /** Returns the singleton instance of the MongoManager */
  public static getInstance(
    dbConfig?: DBConfig,
    networkConfig?: NetworkConfig
  ): MongoManager {
    if (!MongoManager.singletonInstance && dbConfig && networkConfig) {
      MongoManager.singletonInstance = new MongoManager(dbConfig, networkConfig)
    } else if (
      !MongoManager.singletonInstance &&
      (!dbConfig || !networkConfig)
    ) {
      throw new Error(
        'No mongo manager available and no creation parameters supplied'
      )
    }

    return MongoManager.singletonInstance
  }

  createConnection(loadInitialUsers: () => void) {
    let url: string = `mongodb://${this.docConfig.host}:${this.docConfig.port}/?replicaSet=rs0`
    this.logger.verbose('Mongo:', this.host, url)
    this.mongoClient = new MongoClient(url)
    this.mongoClient.connect((err, client) => {
      //Connect to mongodb
      if (err) {
        this.logger.error('in Doc DB connect:', err?.stack)
        //TODO remove console.logs
        console.log('Error connecting to mongo:', err, err?.stack)
        return
      } else if (client == undefined) {
        this.logger.error('Client undefined in Doc DB connect')
        console.log('Mongo client is undefined!')
        return
      } else {
        this.logger.info('Connected to mongo simulation database')
        console.log('Connected to Mongo!')
      }

      this.dbConnection = client.db(this.docConfig.database)

      this.accountsCollection = this.dbConnection.collection('accounts')

      this.analyticsLiftCollection = this.dbConnection.collection('lifts')
      this.analyticsServerCollection = this.dbConnection.collection('servers')
      //      this.docAg.createIndex({peer_cid: 1}, {unique: true})		//Should be multicolumn: cid, host
      //      this.docAg.countDocuments((e,r)=>{if (!e) this.worldPop = r})	//Actual people in doc DB
      this.logger.trace('Connected to mongo simulation DB')

      loadInitialUsers()
    })
  }

  isDBClientConnected(): boolean {
    return this.mongoClient != null
  }

  updateOneAccount(account: AccountData) {
    // console.log("Putting into mongo:\n", account)
    this.accountsCollection.updateOne(
      { peer_cid: account.peer_cid, host: account.peer_host },
      { $set: account },
      { upsert: true },
      (e, r) => {
        if (e) {
          this.logger.error(e.message)
          console.log('Error updating account:', account.std_name, e)
        } else {
          this.logger.trace('Add/update account:', r)
          console.log(account.peer_cid, 'added to mongo!')
        }
      }
    )
  }

  findPeerAndUpdate(
    hostedAccountPeerCid: string,
    alreadyConnectedAccounts: string[],
    callback: (peerData: AccountData | any) => void
  ) {
    const maxFoils = 5
    const query = {
      //Look for a trading partner
      peer_cid: {
        $ne: hostedAccountPeerCid, //Don't find myself
        $nin: alreadyConnectedAccounts, //Or anyone I'm already connected to
      },
      foils: { $lte: maxFoils }, //Or those with not too many foils already
      pendingPartners: {
        $ne: hostedAccountPeerCid, //Or anyone I have a pending connection with
      },
    }

    const update = {
      $set: { random: Math.random() }, //re-randomize this person
      $inc: { foils: 1 }, //And make it harder to get them again next time
      $push: { pendingPartners: hostedAccountPeerCid }, //Immediately add ourselves to the array to avoid double connecting
    }

    const options = {
      //Sort by
      sort: { foils: 1, random: -1 },
    }

    this.accountsCollection
      //@ts-ignore
      .findOneAndUpdate(query, update, options)
      .then(
        (res) => {
          if (res.ok) {
            this.logger.verbose(
              '  Best peer:',
              res?.value?.std_name,
              res?.value?.host
            )
            callback(res.value)
          } else {
            this.logger.info('  No peer found:')
            callback(null)
          }
        },
        (err) => {
          this.logger.error('  Error finding a peer:', err)
        }
      )
      .catch((reason) => {
        this.logger.info(' No peer found:', reason)
      })
  }

  deleteAllAccountsExcept(accountsToKeep: string[]): void {
    this.accountsCollection.deleteMany(
      {
        //Delete any strays left in world db
        host: this.host,
        peer_cid: { $nin: accountsToKeep },
      },
      (e, r) => {
        if (e) this.logger.error(e.message)
        else this.logger.debug('Delete accounts in world:', r)
      }
    )
  }

  analyticsAddLift(lift: Lift) {
    this.analyticsLiftCollection.insertOne(lift)
  }

  analyticsAddServer(server: Server) {
    this.analyticsServerCollection.insertOne(server)
  }
}

export default MongoManager

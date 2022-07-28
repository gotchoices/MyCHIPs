import { MongoClient, Db, Collection, Document } from 'mongodb'
import Os from 'os'
import UnifiedLogger from './unifiedLogger'
import { Lift, Server } from '../@types/models'
import WorldManagerInterface from './worldManagerInterface'

class MongoManager implements WorldManagerInterface {
  private static singletonInstance: MongoManager
  private docConfig: DDConfig
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

  private constructor(dbConfig: DDConfig, argv) {
    this.docConfig = Object.assign({}, {
      host:'localhost', port: 27017, database: 'mychips'
    }, dbConfig)
    this.logger = UnifiedLogger.getInstance()

    // MongoDB host name
    this.host = argv.peerServer || Os.hostname()

    this.foreignActionTagIndex = 0
    this.foreignActionCallbackCache = {}
  }

  /** Returns the singleton instance of the MongoManager */
  public static getInstance(
    dbConfig?: DDConfig,
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
    let url: string = `mongodb://${this.docConfig.host}:${this.docConfig.port}`
    this.logger.verbose('Mongo:', this.host, url)
    this.mongoClient = new MongoClient(url, {useUnifiedTopology: true})
    this.mongoClient.connect((err, client) => {
      //Connect to mongodb
      if (err) {
        this.logger.error('in Doc DB connect:', err?.stack)
        return
      } else if (client == undefined) {
        this.logger.error('Client undefined in Doc DB connect')
        return
      } else {
        this.logger.trace('Connected to mongo simulation database')
      }

      this.dbConnection = client.db(this.docConfig.database)

      this.accountsCollection = this.dbConnection.collection('entities')

      this.analyticsLiftCollection = this.dbConnection.collection('lifts')
      this.analyticsServerCollection = this.dbConnection.collection('servers')
      //      this.docAg.createIndex({peer_cid: 1}, {unique: true})		//Should be multicolumn: cid, host
      //      this.docAg.countDocuments((e,r)=>{if (!e) this.worldPop = r})	//Actual people in doc DB
      this.logger.trace('Connected to mongo simulation DB')

      loadInitialUsers()
    })
  }

  closeConnection() {
    this.mongoClient.close()
  }

  isDBClientConnected(): boolean {
    return this.mongoClient != null
  }

  updateOneAccount(account: AccountData) {
    this.accountsCollection.updateOne(
      { peer_cid: account.peer_cid, host: account.peer_host },
      { $set: account },
      { upsert: true },
      (e, r) => {
        if (e) {
          this.logger.error(e.message)
        } else {
          this.logger.trace('Add/update mongo account:', r)
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
//Fixme: Can re-enable this, but we first need a way/place to clear pendingPartners
//       particularly at the beginning when initializing the database.  We should also
//       clear out a single cid when connection is made and moves to alreadyConnectedAccounts
//      pendingPartners: {
//        $ne: hostedAccountPeerCid, //Or anyone I have a pending connection with
//      },
    }

    const update = {
      $set: { random: Math.random() }, //re-randomize this person
      $inc: { foils: 1 }, //And make it harder to get them again next time
//Fixme: part of Fixme above
//      $push: { pendingPartners: hostedAccountPeerCid }, //Immediately add ourselves to the array to avoid double connecting
    }

    const options = {
      //Sort by
      sort: { foils: 1, random: -1 },
    }
//this.logger.debug('Mongo query:', JSON.stringify(query))
    this.accountsCollection
      //@ts-ignore
      .findOneAndUpdate(query, update, options)
      .then(
        (res) => {
//this.logger.debug('ZZ:', JSON.stringify(res))
          if (res.ok && res && res.value) {
            this.logger.debug(
              '  Best peer:',
              res?.value?.peer_cid,
              res?.value?.agent
            )
            callback(res.value)
          } else {
            this.logger.error('  No peer result from mongo')
            callback(null)
          }
        },
        (err) => {
          this.logger.error('  Error finding a peer:', err)
        }
      )
      .catch((err) => {
        this.logger.error('Error in mongo query:', err.message)
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

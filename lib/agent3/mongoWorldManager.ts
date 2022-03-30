import { MongoClient, Db, Collection, Document, ChangeStream } from 'mongodb'
import Os from 'os'
import { ActionDoc } from '../@types/document'
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
  private actionsCollection!: Collection<ActionDoc>
  private accountsCollection!: Collection<Document> //TODO: Change this
  private analyticsLiftCollection!: Collection<Document>
  private analyticsServerCollection!: Collection<Document>
  private actionsCollectionStream!: ChangeStream<ActionDoc>

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

  createConnection(
    notifyOfNewAccountRequest: (
      accountData: AccountData,
      tag: string,
      destHost: string
    ) => void,
    loadInitialUsers: () => void
  ) {
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

      this.actionsCollection = this.dbConnection.collection('actions')
      //      this.actionsCollectionStream = this.actionsCollection.watch([{$match: { host: null }}])
      this.actionsCollectionStream = this.actionsCollection.watch([
        { $match: { 'fullDocument.host': this.host } },
      ]) //Receive async updates for this host
      this.actionsCollectionStream.on('error', (error) => {
        this.logger.error("Couldn't watch mongo:", this.host, error)
      })
      this.actionsCollectionStream.on('change', (change) => {
        //Handle async notices from doc DB
        const doc = change.fullDocument
        if (doc === undefined) return
        this.logger.debug('Got change:', doc.action, doc.host, doc.data)
        // Check if Action Request is for us
        //FIXME: Maybe there's some actions that all servers should listen to.
        // If so, we can change this
        if (doc.host != this.host) return

        if (doc.action == 'createAccount') {
          // Someone asking me to insert a peer into the DB
          notifyOfNewAccountRequest(doc.data!, doc.tag, doc.from)
        } else if (doc.action == 'done') {
          // Someone has told me that an action I requested is done
          this.logger.debug('Remote call done:', doc.tag, 'from:', doc.from)
          console.log('Remote action done:', doc.tag, 'target:', doc.from)
          this.foreignActionCallbackCache[doc.tag]()
          delete this.foreignActionCallbackCache[doc.tag]
        }
        // Add other types of Foreign Actions here

        //Delete signaling record
        this.actionsCollection.deleteOne({ _id: doc._id })
      })

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

  insertAction(
    command: string,
    tag: string = this.host + '.' + this.foreignActionTagIndex++,
    destinationHost: string,
    data?: any,
    callback?: () => void
  ) {
    console.log('Adding', command, 'action to db...')
    if (data) console.log('with data')
    if (callback) console.log('and callback')
    this.actionsCollection.insertOne(
      {
        action: command,
        tag: tag,
        host: destinationHost,
        from: this.host,
        data: data,
      },
      (err, res) => {
        if (err) {
          this.logger.error(
            'Sending remote command:',
            command,
            'to:',
            destinationHost
          )
          console.log('Error adding action to db:', err)
        } else {
          this.logger.info(
            'Sent remote action:',
            command,
            'to:',
            destinationHost
          )
          console.log('Added', command, 'action for', destinationHost)
        }
      }
    )

    if (callback) {
      this.foreignActionCallbackCache[tag] = callback
    }
  }

  updateOneAccount(account: AccountData) {
    // console.log("Putting into mongo:\n", account)
    this.accountsCollection.updateOne(
      { peer_cid: account.peer_cid, host: account.host },
      { $set: account },
      { upsert: true },
      (e, r) => {
        if (e) {
          this.logger.error(e.message)
          console.log('Error updating account:', account.std_name, e)
        } else {
          this.logger.trace('Add/update account:', r)
          console.log('Account', account.std_name, 'added to mongo!')
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
    }

    const update = {
      $set: { random: Math.random() }, //re-randomize this person
      $inc: { foils: 1 }, //And make it harder to get them again next time
      //TODO: convert to PushDocument type somehow
      $push: { partners: hostedAccountPeerCid }, //Immediately add ourselves to the array to avoid double connecting
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

import { MongoClient, Db, Collection, Document, ChangeStream } from 'mongodb'
import Os from 'os'
import { ActionDoc, PeerDoc } from '../@types/document'
import UnifiedLogger from './unifiedLogger'

class MongoManager {
  private static singletonInstance: MongoManager
  private dbConfig: DBConfig
  private host: string
  private logger: WyclifLogger
  private dbConnection!: Db

  private mongoClient!: MongoClient
  private actionsCollection!: Collection<ActionDoc>
  private agentsCollection!: Collection<Document> //TODO: Change this
  private actionsCollectionStream!: ChangeStream<ActionDoc>

  /** A cache in which to store callbacks that need to run when actions sent to foreign servers are completed */
  private foreignActionCallbackCache!: { [x: string]: (...args: any[])=> any }
  private foreignActionTagIndex!: number

  private constructor(dbConfig: DBConfig, argv) {
    this.dbConfig = dbConfig
    this.logger = UnifiedLogger.getInstance()

    // MongoDB host name
    this.host = argv.peerServer || Os.hostname()

    this.foreignActionTagIndex = 0
  }

  /** Returns the singleton instance of the MongoManager */
  public static getInstance(dbConfig?: DBConfig, networkConfig?: NetworkConfig): MongoManager {
    if (!MongoManager.singletonInstance && dbConfig && networkConfig) {
      MongoManager.singletonInstance = new MongoManager(dbConfig, networkConfig)
    }
    else if (!MongoManager.singletonInstance && (!dbConfig || !networkConfig)) {
      throw new Error('No mongo manager available and no creation parameters supplied')
    }

    return MongoManager.singletonInstance
  }

  createConnection(
    options,
    notifyOfNewAgentRequest,
    loadInitialUsers
  ) {
    let url = `mongodb://${this.dbConfig.host}:${this.dbConfig.port}/?replicaSet=rs0`
    this.logger.verbose('Mongo:', this.host, url)
    this.mongoClient = new MongoClient(url, options)
    this.mongoClient.connect((err, client) => {
      //Connect to mongodb
      if (err) {
        this.logger.error('in Doc DB connect:', err?.stack)
        return
      }
      if (client == undefined) {
        this.logger.error('Client undefined in Doc DB connect')
        return
      }

      this.dbConnection = client.db(this.dbConfig.database)

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

        if (doc.action == 'createUser') {
          // Someone asking me to insert a peer into the DB
          notifyOfNewAgentRequest(doc.data!, doc.tag, doc.from)
        } else if (doc.action == 'done') {
          // Someone has told me that an action I requested is done
          this.logger.debug('Remote call done:', doc.tag, 'from:', doc.from)
          this.foreignActionCallbackCache[doc.tag]()
          delete this.foreignActionCallbackCache[doc.tag]
        }
        // Add other types of Foreign Actions here

        //Delete signaling record
        this.actionsCollection.deleteOne({ _id: doc._id }) 
      })

      this.agentsCollection = this.dbConnection.collection('agents')
      //      this.docAg.createIndex({peer_cid: 1}, {unique: true})		//Should be multicolumn: cid, host
      //      this.docAg.countDocuments((e,r)=>{if (!e) this.worldPop = r})	//Actual people in doc DB
      this.logger.trace('Connected to doc DB')

      loadInitialUsers()
    })
  }

  isDBClientConnected(): boolean {
    return this.mongoClient != null
  }

  insertAction(cmd: string, tag: string = this.host + '.' + this.foreignActionTagIndex++, destinationHost: string, callback?) {
    this.actionsCollection.insertOne(
      { action: cmd, tag: tag, host: destinationHost, from: this.host },
      (err, res) => {
        if (err) this.logger.error('Sending remote command:', cmd, 'to:', destinationHost)
        else this.logger.info('Sent remote action:', cmd, 'to:', destinationHost)
      }
    )
    
    if (callback) {
      this.foreignActionCallbackCache[tag] = callback
    }
  }

  updateOneAgent(agent: AgentData) {
    agent.host = this.host //Mark user as belonging to us

    this.agentsCollection.updateOne(
      { peer_cid: agent.peer_cid, host: agent.host },
      { $set: agent },
      { upsert: true },
      (e, r) => {
        if (e) this.logger.error(e.message)
        else this.logger.trace('Add/update agent:', r)
      }
    )
  }

  findPeerAndUpdate(hostedAccountPeerCid: string, alreadyConnectedAccounts: string[]): any {
    let result: any = undefined
    this.agentsCollection.findOneAndUpdate(
      {
        //Look for a trading partner
        peer_cid: {
          $ne: hostedAccountPeerCid, //Don't find myself
          $nin: alreadyConnectedAccounts, //Or anyone I'm already connected to
        }
      },
      {
        $set: { random: Math.random() }, //re-randomize this person
        $inc: { foils: 1 }, //And make it harder to get them again next time
        $push: { partners: hostedAccountPeerCid }, //Immediately add ourselves to the array to avoid double connecting
      },
      {
        //Sort by
        sort: { foils: 1, random: -1 },
      },
      (e, res) => {
        //Get result of query
        if (e) {
          this.logger.error(e.message)
          throw "Error trying to find another peer"
        } else if (res?.ok) {
          this.logger.verbose(
            '  Best client:',
            res?.value?.std_name,
            res?.value?.host
          )
          result = res.value
        } else {
          this.logger.verbose('  No client found in world DB')
        }
      }
    )

    return result
  }

  deleteManyAgents(processedAgents: string[]): void {
    this.agentsCollection.deleteMany(
      {
        //Delete any strays left in world db
        host: this.host,
        peer_cid: { $nin: processedAgents },
      },
      (e, r) => {
        if (e) this.logger.error(e.message)
        else this.logger.debug('Delete agents in world:', r)
      }
    )
  }
}

export default MongoManager

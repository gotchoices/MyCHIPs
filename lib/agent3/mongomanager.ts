import Agent from './agent'
import {
  MongoClient,
  Db,
  Collection,
  Document,
  ChangeStream,
  MongoClientOptions,
  PushOperator,
} from 'mongodb'
import Os from 'os'
import { ActionDoc, PeerDoc } from '../@types/document'
import UnifiedLogger from './unifiedLogger'

class MongoManager {
  private static singletonInstance: MongoManager
  private docConfig: DBConfig
  private host: string
  private logger: WyclifLogger
  private dbConnection!: Db

  private mongoClient!: MongoClient
  private actionsCollection!: Collection<ActionDoc>
  private agentsCollection!: Collection<Document> //TODO: Change this
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
    notifyOfNewAgentRequest: (
      agentData: AgentData,
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
        console.log("Error connecting to mongo:", err, err?.stack)
        return
      }
      if (client == undefined) {
        this.logger.error('Client undefined in Doc DB connect')
        console.log("Mongo client is undefined!")
        return
      }

      console.log("Connected to Mongo!")

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

  insertAction(
    command: string,
    tag: string = this.host + '.' + this.foreignActionTagIndex++,
    destinationHost: string,
    callback?: () => void
  ) {
    console.log("Attempting to add", command, "action to db...")
    this.actionsCollection.insertOne(
      { action: command, tag: tag, host: destinationHost, from: this.host },
      (err, res) => {
        if (err) {
          this.logger.error(
            'Sending remote command:',
            command,
            'to:',
            destinationHost
          )
          console.log("Error adding action to db:", err)
        }
        else {
          this.logger.info(
            'Sent remote action:',
            command,
            'to:',
            destinationHost
          )
          console.log("Added", command, "action to db!")
        }
      }
    )

    if (callback) {
      this.foreignActionCallbackCache[tag] = callback
    }
  }

  updateOneAgent(agent: AgentData) {
    this.agentsCollection.updateOne(
      { peer_cid: agent.peer_cid, host: agent.host },
      { $set: agent },
      { upsert: true },
      (e, r) => {
        if (e) {
          this.logger.error(e.message)
          console.log("Error updating agent:", agent.std_name, e)
        }
        else {
          this.logger.trace('Add/update agent:', r)
          console.log("Agent", agent.std_name, "updated in mongo!")
        }
      }
    )

  }

  findPeerAndUpdate(
    hostedAccountPeerCid: string,
    alreadyConnectedAccounts: string[],
    callback: (peerData: AgentData | any) => void
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
    // @ts-ignore
    this.agentsCollection.findOneAndUpdate(query, update, options)
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
    ).catch((reason) => {
      this.logger.error(' No peer found:', reason)
    })
  }

  deleteAllAgentsExcept(agentsToKeep: string[]): void {
    this.agentsCollection.deleteMany(
      {
        //Delete any strays left in world db
        host: this.host,
        peer_cid: { $nin: agentsToKeep },
      },
      (e, r) => {
        if (e) this.logger.error(e.message)
        else this.logger.debug('Delete agents in world:', r)
      }
    )
  }
}

export default MongoManager

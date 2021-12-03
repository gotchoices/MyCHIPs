const DocClient = require('mongodb').MongoClient
const Os = require('os')

module.exports = class MongoManager {
  #docConfig
  #host
  #logger
  #dbConnection

  #mongoClient
  #actionsCollection
  #actionsCollectionStream
  #agentsCollection

  constructor(config, logger, argv) {
    this.#docConfig = config
    this.#logger = logger

    // MongoDB host name
    this.#host = argv.peerServer || Os.hostname()
  }

  createConnection(options, checkPeer, notifyOfActionDone, loadInitialUsers) {
    let url = `mongodb://${this.#docConfig.host}:${
      this.#docConfig.port
    }/?replicaSet=rs0`
    this.#logger.verbose('Mongo:', this.#host, url)
    this.#dbConnection = new DocClient(url, options)

    this.#dbConnection.connect((err, client) => {
      //Connect to mongodb
      if (err) {
        this.#logger.error('in Doc DB connect:', err.stack)
        return
      }
      this.#mongoClient = client.db(this.#docConfig.database)

      this.#actionsCollection = this.#mongoClient.collection('actions')
      //      this.actionsCollectionStream = this.actionsCollection.watch([{$match: { host: null }}])
      this.#actionsCollectionStream = this.#actionsCollection.watch([
        { $match: { 'fullDocument.host': this.#host } },
      ]) //Receive async updates for this host
      this.#actionsCollectionStream.on('error', (ev) => {
        this.#logger.error("Couldn't watch mongo:", this.#host, ev)
      })

      this.#actionsCollectionStream.on('change', (ev) => {
        //Handle async notices from doc DB
        let doc = ev ? ev.fullDocument : {}
        this.#logger.debug('Got change:', doc.action, doc.host, doc.data)
        if (doc.action == 'createUser') {
          //Someone asking me to insert a peer into the DB
          checkPeer(doc.data, (pDat) => {
            this.#logger.debug('Peer added/OK:', pDat.peer_cid, 'notifying:', doc.data.host)
            this.#actionsCollection.insertOne(
              {
                action: 'done',
                tag: doc.tag,
                host: doc.data.host,
                from: this.#host,
              },
              () => {}
            )
          })
        } else if (doc.action == 'done') {
          notifyOfActionDone(doc)
        }
        this.#actionsCollection.deleteOne({ _id: doc._id }) //Delete signaling record
      })

      this.#agentsCollection = this.#mongoClient.collection('agents')
      //      this.docAg.createIndex({peer_cid: 1}, {unique: true})		//Should be multicolumn: cid, host
      //      this.docAg.countDocuments((e,r)=>{if (!e) this.worldPop = r})	//Actual people in doc DB
      this.#logger.trace('Connected to doc DB')

      loadInitialUsers()
    })
    this.#logger.info("Mongo Connection Created")
  }

  isDBClientConnected() {
    return this.#mongoClient != null
  }

  insertAction(cmd, tag, host, data) {
    this.#actionsCollection.insertOne(
      { action: cmd, tag, host, from: this.#host, data },
      null,
      (err, res) => {
        if (err) this.#logger.error('Sending remote command:', cmd, 'to:', host)
      }
    )
  }

  updateOneAgent(row) {
    row.host = this.#host //Mark user as belonging to us

    this.#agentsCollection.updateOne(
      { peer_cid: row.peer_cid, host: row.host },
      { $set: row },
      { upsert: true },
      (e, r) => {
        if (e) this.#logger.error(e.message)
        else this.#logger.trace('Add/update agent:', r)
      }
    )
  }

  //TODO change name
  findOneAndUpdate(aData, maxfoils, notifyTryTally) {
    this.#agentsCollection.findOneAndUpdate(
      {
        //Look for a trading partner
        peer_cid: {
          $ne: aData.peer_cid, //Don't find myself
          $nin: aData.partners, //Or anyone I'm already connected to
        },
        //        host: {$ne: this.host},			//Look only on other hosts
        foils: { $lte: maxfoils }, //Or those with not too many foils already
      },
      {
        $set: { random: Math.random() }, //re-randomize this person
        $inc: { foils: 1 }, //And make it harder to get them again next time
        $push: { partners: aData.peer_cid }, //Immediately add ourselves to the array to avoid double connecting
      },
      {
        //Sort by
        sort: { foils: 1, random: -1 },
      },
      (e, res) => {
        //Get result of query
        if (e) {
          this.#logger.error(e.errmsg)
        } else if (res.ok) {
          this.#logger.verbose('  Best client:', res.value.std_name, res.value.host)
          notifyTryTally(aData, res.value)
        } else {
          this.#logger.verbose('  No client found in world DB')
        }
      }
    ) //findOneAndUpdate
  }

  deleteManyAgents(haveEm) {
    this.#agentsCollection.deleteMany(
      {
        //Delete any strays left in world db
        host: this.#host,
        peer_cid: { $nin: haveEm },
      },
      (e, r) => {
        if (e) this.#logger.error(e.message)
        else this.#logger.debug('Delete agents in world:', r.n)
      }
    )
  }

  updateAgents() {}
}

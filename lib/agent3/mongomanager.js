const DocClient = require('mongodb').MongoClient

module.exports = class MongoManager {
  #docConfig
  #host
  #log
  #dbConnection

  #mongoClient
  #actionsCollection
  #actionsCollectionStream
  #agentsCollection

  constructor(config, log) {
    this.#config = config
    this.#log = log

    // MongoDB host name
    this.host = argv.peerServer || Os.hostname()
    this.log.info('Initializing agent model controller 2 on:', this.host)
  }

  createConnection(options, loadInitialUsers) {
    let url = `mongodb://${this.#docConfig.host}:${
      this.#docConfig.port
    }/?replicaSet=rs0`
    this.#log.verbose('Mongo:', this.#host, url)
    this.#dbConnection = new DocClient(url, options)

    this.#dbConnection.connect((err, client) => {
      //Connect to mongodb
      if (err) {
        this.#log.error('in Doc DB connect:', err.stack)
        return
      }
      this.#mongoClient = client.db(this.#docConfig.database)

      this.#actionsCollection = this.#mongoClient.collection('actions')
      //      this.actionsCollectionStream = this.actionsCollection.watch([{$match: { host: null }}])
      this.#actionsCollectionStream = this.#actionsCollection.watch([
        { $match: { 'fullDocument.host': this.#host } },
      ]) //Receive async updates for this host
      this.#actionsCollectionStream.on('error', (ev) => {
        this.#log.error("Couldn't watch mongo:", this.#host, ev)
      })

      this.#actionsCollectionStream.on('change', (ev) => {
        //Handle async notices from doc DB
        let doc = ev ? ev.fullDocument : {}
        this.#log.debug('Got change:', doc.action, doc.host, doc.data)
        if (doc.action == 'createUser') {
          //Someone asking me to insert a peer into the DB
          this.checkPeer(doc.data, (pDat) => {
            this.#log.debug(
              'Peer added/OK:',
              pDat.peer_cid,
              'notifying:',
              doc.data.host
            )
            this.actionsCollection.insertOne(
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
          //Remote action has completed
          this.#log.debug('Remote call done:', doc.tag, 'from:', doc.from)
          if (this.remoteCBs[doc.tag]) {
            //If I can find a stored callback
            this.remoteCBs[doc.tag]() //Call it
            delete this.remoteCBs[doc.tag] //And then forget about it
          }
        }
        this.#actionsCollection.deleteOne({ _id: doc._id }) //Delete signaling record
      })

      this.#agentsCollection = this.#mongoClient.collection('agents')
      //      this.docAg.createIndex({peer_cid: 1}, {unique: true})		//Should be multicolumn: cid, host
      //      this.docAg.countDocuments((e,r)=>{if (!e) this.worldPop = r})	//Actual people in doc DB
      this.#log.trace('Connected to doc DB')

      loadInitialUsers()
    })
  }

  updateAgents() {}
}

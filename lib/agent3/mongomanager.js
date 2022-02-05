"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const mongodb_1 = require("mongodb");
const os_1 = __importDefault(require("os"));
const unifiedLogger_1 = __importDefault(require("./unifiedLogger"));
class MongoManager {
    constructor(dbConfig, argv) {
        this.docConfig = dbConfig;
        this.logger = unifiedLogger_1.default.getInstance();
        // MongoDB host name
        this.host = argv.peerServer || os_1.default.hostname();
        this.foreignActionTagIndex = 0;
    }
    /** Returns the singleton instance of the MongoManager */
    static getInstance(dbConfig, networkConfig) {
        if (!MongoManager.singletonInstance && dbConfig && networkConfig) {
            MongoManager.singletonInstance = new MongoManager(dbConfig, networkConfig);
        }
        else if (!MongoManager.singletonInstance && (!dbConfig || !networkConfig)) {
            throw new Error('No mongo manager available and no creation parameters supplied');
        }
        return MongoManager.singletonInstance;
    }
    createConnection(notifyOfNewAgentRequest, loadInitialUsers) {
        let url = `mongodb://${this.docConfig.host}:${this.docConfig.port}/?replicaSet=rs0`;
        this.logger.verbose('Mongo:', this.host, url);
        this.mongoClient = new mongodb_1.MongoClient(url);
        this.mongoClient.connect((err, client) => {
            //Connect to mongodb
            if (err) {
                this.logger.error('in Doc DB connect:', err === null || err === void 0 ? void 0 : err.stack);
                return;
            }
            if (client == undefined) {
                this.logger.error('Client undefined in Doc DB connect');
                return;
            }
            this.dbConnection = client.db(this.docConfig.database);
            this.actionsCollection = this.dbConnection.collection('actions');
            //      this.actionsCollectionStream = this.actionsCollection.watch([{$match: { host: null }}])
            this.actionsCollectionStream = this.actionsCollection.watch([
                { $match: { 'fullDocument.host': this.host } },
            ]); //Receive async updates for this host
            this.actionsCollectionStream.on('error', (error) => {
                this.logger.error("Couldn't watch mongo:", this.host, error);
            });
            this.actionsCollectionStream.on('change', (change) => {
                //Handle async notices from doc DB
                const doc = change.fullDocument;
                if (doc === undefined)
                    return;
                this.logger.debug('Got change:', doc.action, doc.host, doc.data);
                // Check if Action Request is for us
                //FIXME: Maybe there's some actions that all servers should listen to. 
                // If so, we can change this
                if (doc.host != this.host)
                    return;
                if (doc.action == 'createAccount') {
                    // Someone asking me to insert a peer into the DB
                    notifyOfNewAgentRequest(doc.data, doc.tag, doc.from);
                }
                else if (doc.action == 'done') {
                    // Someone has told me that an action I requested is done
                    this.logger.debug('Remote call done:', doc.tag, 'from:', doc.from);
                    this.foreignActionCallbackCache[doc.tag]();
                    delete this.foreignActionCallbackCache[doc.tag];
                }
                // Add other types of Foreign Actions here
                //Delete signaling record
                this.actionsCollection.deleteOne({ _id: doc._id });
            });
            this.agentsCollection = this.dbConnection.collection('agents');
            //      this.docAg.createIndex({peer_cid: 1}, {unique: true})		//Should be multicolumn: cid, host
            //      this.docAg.countDocuments((e,r)=>{if (!e) this.worldPop = r})	//Actual people in doc DB
            this.logger.trace('Connected to doc DB');
            loadInitialUsers();
        });
    }
    isDBClientConnected() {
        return this.mongoClient != null;
    }
    insertAction(command, tag = this.host + '.' + this.foreignActionTagIndex++, destinationHost, callback) {
        this.actionsCollection.insertOne({ action: command, tag: tag, host: destinationHost, from: this.host }, (err, res) => {
            if (err)
                this.logger.error('Sending remote command:', command, 'to:', destinationHost);
            else
                this.logger.info('Sent remote action:', command, 'to:', destinationHost);
        });
        if (callback) {
            this.foreignActionCallbackCache[tag] = callback;
        }
    }
    updateOneAgent(agent) {
        this.agentsCollection.updateOne({ peer_cid: agent.peer_cid, host: agent.host }, { $set: agent }, { upsert: true }, (e, r) => {
            if (e)
                this.logger.error(e.message);
            else
                this.logger.trace('Add/update agent:', r);
        });
    }
    findPeerAndUpdate(hostedAccountPeerCid, alreadyConnectedAccounts) {
        let result = undefined;
        this.agentsCollection.findOneAndUpdate({
            //Look for a trading partner
            peer_cid: {
                $ne: hostedAccountPeerCid,
                $nin: alreadyConnectedAccounts, //Or anyone I'm already connected to
            }
        }, {
            $set: { random: Math.random() },
            //TODO: convert to PushDocument type somehow
            $push: { partners: hostedAccountPeerCid }, //Immediately add ourselves to the array to avoid double connecting
        }, {
            //Sort by
            sort: { foils: 1, random: -1 },
        }, (e, res) => {
            var _a, _b;
            //Get result of query
            if (e) {
                this.logger.error(e.message);
                throw "Error trying to find another peer";
            }
            else if (res === null || res === void 0 ? void 0 : res.ok) {
                this.logger.verbose('  Best client:', (_a = res === null || res === void 0 ? void 0 : res.value) === null || _a === void 0 ? void 0 : _a.std_name, (_b = res === null || res === void 0 ? void 0 : res.value) === null || _b === void 0 ? void 0 : _b.host);
                result = res.value;
            }
            else {
                this.logger.verbose('  No client found in world DB');
            }
        });
        return result;
    }
    deleteAllAgentsExcept(agentsToKeep) {
        this.agentsCollection.deleteMany({
            //Delete any strays left in world db
            host: this.host,
            peer_cid: { $nin: agentsToKeep },
        }, (e, r) => {
            if (e)
                this.logger.error(e.message);
            else
                this.logger.debug('Delete agents in world:', r);
        });
    }
}
exports.default = MongoManager;

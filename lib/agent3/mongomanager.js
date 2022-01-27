"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const mongodb_1 = require("mongodb");
const os_1 = __importDefault(require("os"));
const unifiedLogger_1 = __importDefault(require("./unifiedLogger"));
class MongoManager {
    constructor(config, argv) {
        this.docConfig = config;
        this.logger = unifiedLogger_1.default.getInstance();
        // MongoDB host name
        this.host = argv.peerServer || os_1.default.hostname();
    }
    /** Returns the singleton instance of the MongoManager */
    static getInstance(config, argv) {
        if (!MongoManager.singletonInstance) {
            MongoManager.singletonInstance = new MongoManager(config, argv);
        }
        return MongoManager.singletonInstance;
    }
    createConnection(checkPeer, notifyOfActionDone, loadInitialUsers) {
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
                if (doc.action == 'createUser') {
                    //Someone asking me to insert a peer into the DB
                    checkPeer(doc.data, (agentData) => {
                        var _a, _b;
                        this.logger.debug('Peer added/OK:', agentData.peer_cid, 'notifying:', (_a = doc.data) === null || _a === void 0 ? void 0 : _a.host);
                        this.actionsCollection.insertOne({
                            action: 'done',
                            tag: doc.tag,
                            host: (_b = doc.data) === null || _b === void 0 ? void 0 : _b.host,
                            from: this.host,
                        }, () => { });
                    });
                }
                else if (doc.action == 'done') {
                    notifyOfActionDone(doc);
                }
                this.actionsCollection.deleteOne({ _id: doc._id }); //Delete signaling record
            });
            this.agentsCollection = this.dbConnection.collection('agents');
            //      this.docAg.createIndex({peer_cid: 1}, {unique: true})		//Should be multicolumn: cid, host
            //      this.docAg.countDocuments((e,r)=>{if (!e) this.worldPop = r})	//Actual people in doc DB
            this.logger.trace('Connected to doc DB');
            loadInitialUsers();
        });
        this.logger.info('Mongo Connection Created');
    }
    isDBClientConnected() {
        return this.mongoClient != null;
    }
    insertAction(command, tag, host, data) {
        this.actionsCollection.insertOne({ action: command, tag, host, from: this.host, data }, 
        // @ts-ignore
        undefined, (err, _res) => {
            if (err)
                this.logger.error('Sending remote command:', command, 'to:', host);
        });
    }
    updateOneAgent(row) {
        row.host = this.host; //Mark user as belonging to us
        this.agentsCollection.updateOne({ peer_cid: row.peer_cid, host: row.host }, { $set: row }, { upsert: true }, (e, r) => {
            if (e)
                this.logger.error(e.message);
            else
                this.logger.trace('Add/update agent:', r);
        });
    }
    //TODO change name
    findOneAndUpdate(agentData, maxfoils, notifyTryTally) {
        this.agentsCollection.findOneAndUpdate({
            //Look for a trading partner
            peer_cid: {
                $ne: agentData.peer_cid,
                $nin: agentData.partners, //Or anyone I'm already connected to
            },
            //        host: {$ne: this.host},			//Look only on other hosts
            foils: { $lte: maxfoils }, //Or those with not too many foils already
        }, {
            $set: { random: Math.random() },
            $inc: { foils: 1 },
            $push: { partners: agentData.peer_cid }, //Immediately add ourselves to the array to avoid double connecting
        }, {
            //Sort by
            sort: { foils: 1, random: -1 },
        }, (e, res) => {
            var _a, _b;
            //Get result of query
            if (e) {
                this.logger.error(e.message);
            }
            else if (res === null || res === void 0 ? void 0 : res.ok) {
                this.logger.verbose('  Best client:', (_a = res === null || res === void 0 ? void 0 : res.value) === null || _a === void 0 ? void 0 : _a.std_name, (_b = res === null || res === void 0 ? void 0 : res.value) === null || _b === void 0 ? void 0 : _b.host);
                notifyTryTally(agentData, res.value);
            }
            else {
                this.logger.verbose('  No client found in world DB');
            }
        }); //findOneAndUpdate
    }
    deleteManyAgents(processedAgents) {
        this.agentsCollection.deleteMany({
            //Delete any strays left in world db
            host: this.host,
            peer_cid: { $nin: processedAgents },
        }, (e, r) => {
            if (e)
                this.logger.error(e.message);
            else
                this.logger.debug('Delete agents in world:', r);
        });
    }
    updateAgents() { }
}
exports.default = MongoManager;

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
        this.foreignActionCallbackCache = {};
    }
    /** Returns the singleton instance of the MongoManager */
    static getInstance(dbConfig, networkConfig) {
        if (!MongoManager.singletonInstance && dbConfig && networkConfig) {
            MongoManager.singletonInstance = new MongoManager(dbConfig, networkConfig);
        }
        else if (!MongoManager.singletonInstance &&
            (!dbConfig || !networkConfig)) {
            throw new Error('No mongo manager available and no creation parameters supplied');
        }
        return MongoManager.singletonInstance;
    }
    createConnection(notifyOfNewAccountRequest, loadInitialUsers) {
        let url = `mongodb://${this.docConfig.host}:${this.docConfig.port}/?replicaSet=rs0`;
        this.logger.verbose('Mongo:', this.host, url);
        this.mongoClient = new mongodb_1.MongoClient(url);
        this.mongoClient.connect((err, client) => {
            //Connect to mongodb
            if (err) {
                this.logger.error('in Doc DB connect:', err === null || err === void 0 ? void 0 : err.stack);
                //TODO remove console.logs
                console.log('Error connecting to mongo:', err, err === null || err === void 0 ? void 0 : err.stack);
                return;
            }
            else if (client == undefined) {
                this.logger.error('Client undefined in Doc DB connect');
                console.log('Mongo client is undefined!');
                return;
            }
            else {
                this.logger.info('Connected to mongo simulation database');
                console.log('Connected to Mongo!');
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
                    notifyOfNewAccountRequest(doc.data, doc.tag, doc.from);
                }
                else if (doc.action == 'done') {
                    // Someone has told me that an action I requested is done
                    this.logger.debug('Remote call done:', doc.tag, 'from:', doc.from);
                    console.log('Remote action done:', doc.tag, 'target:', doc.from);
                    this.foreignActionCallbackCache[doc.tag]();
                    delete this.foreignActionCallbackCache[doc.tag];
                }
                // Add other types of Foreign Actions here
                //Delete signaling record
                this.actionsCollection.deleteOne({ _id: doc._id });
            });
            this.accountsCollection = this.dbConnection.collection('accounts');
            this.analyticsLiftCollection = this.dbConnection.collection('lifts');
            this.analyticsServerCollection = this.dbConnection.collection('servers');
            //      this.docAg.createIndex({peer_cid: 1}, {unique: true})		//Should be multicolumn: cid, host
            //      this.docAg.countDocuments((e,r)=>{if (!e) this.worldPop = r})	//Actual people in doc DB
            this.logger.trace('Connected to mongo simulation DB');
            loadInitialUsers();
        });
    }
    isDBClientConnected() {
        return this.mongoClient != null;
    }
    insertAction(command, tag = this.host + '.' + this.foreignActionTagIndex++, destinationHost, data, callback) {
        console.log('Adding', command, 'action to db...');
        if (data)
            console.log('with data');
        if (callback)
            console.log('and callback');
        this.actionsCollection.insertOne({
            action: command,
            tag: tag,
            host: destinationHost,
            from: this.host,
            data: data,
        }, (err, res) => {
            if (err) {
                this.logger.error('Sending remote command:', command, 'to:', destinationHost);
                console.log('Error adding action to db:', err);
            }
            else {
                this.logger.info('Sent remote action:', command, 'to:', destinationHost);
                console.log('Added', command, 'action for', destinationHost);
            }
        });
        if (callback) {
            this.foreignActionCallbackCache[tag] = callback;
        }
    }
    updateOneAccount(account) {
        // console.log("Putting into mongo:\n", account)
        this.accountsCollection.updateOne({ peer_cid: account.peer_cid, host: account.host }, { $set: account }, { upsert: true }, (e, r) => {
            if (e) {
                this.logger.error(e.message);
                console.log('Error updating account:', account.std_name, e);
            }
            else {
                this.logger.trace('Add/update account:', r);
                console.log('Account', account.std_name, 'added to mongo!');
            }
        });
    }
    findPeerAndUpdate(hostedAccountPeerCid, alreadyConnectedAccounts, callback) {
        const maxFoils = 5;
        const query = {
            //Look for a trading partner
            peer_cid: {
                $ne: hostedAccountPeerCid,
                $nin: alreadyConnectedAccounts, //Or anyone I'm already connected to
            },
            foils: { $lte: maxFoils }, //Or those with not too many foils already
        };
        const update = {
            $set: { random: Math.random() },
            $inc: { foils: 1 },
            //TODO: convert to PushDocument type somehow
            $push: { partners: hostedAccountPeerCid }, //Immediately add ourselves to the array to avoid double connecting
        };
        const options = {
            //Sort by
            sort: { foils: 1, random: -1 },
        };
        this.accountsCollection
            //@ts-ignore
            .findOneAndUpdate(query, update, options)
            .then((res) => {
            var _a, _b;
            if (res.ok) {
                this.logger.verbose('  Best peer:', (_a = res === null || res === void 0 ? void 0 : res.value) === null || _a === void 0 ? void 0 : _a.std_name, (_b = res === null || res === void 0 ? void 0 : res.value) === null || _b === void 0 ? void 0 : _b.host);
                callback(res.value);
            }
            else {
                this.logger.info('  No peer found:');
                callback(null);
            }
        }, (err) => {
            this.logger.error('  Error finding a peer:', err);
        })
            .catch((reason) => {
            this.logger.info(' No peer found:', reason);
        });
    }
    deleteAllAccountsExcept(accountsToKeep) {
        this.accountsCollection.deleteMany({
            //Delete any strays left in world db
            host: this.host,
            peer_cid: { $nin: accountsToKeep },
        }, (e, r) => {
            if (e)
                this.logger.error(e.message);
            else
                this.logger.debug('Delete accounts in world:', r);
        });
    }
    analyticsAddLift(lift) {
        this.analyticsLiftCollection.insertOne(lift);
    }
    analyticsAddServer(server) {
        this.analyticsServerCollection.insertOne(server);
    }
}
exports.default = MongoManager;

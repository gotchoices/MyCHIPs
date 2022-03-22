import Account from "../account";
import Lift from "../models/Lift";
import Server from "../models/Server";
import AnalyticsServiceInterface from "./analyticsServiceInterface"
import {
    MongoClient,
    Db,
    Collection,
    Document,
    ChangeStream,
    MongoClientOptions,
    PushOperator,
  } from 'mongodb'
import { DBConfig, WyclifLogger} from '../../@types/global'
import { AnalyticsDoc } from '../../@types/document'

class MongoAnalyticsService implements AnalyticsServiceInterface {
    private static singletonInstance: MongoAnalyticsService
    private dbConfig: DBConfig
    private host: string
    private logger: WyclifLogger
    private dbConnection!: Db
  
    private mongoClient!: MongoClient
    private analyticsCollection!: Collection<AnalyticsDoc>

    private constructor (dbConfig, DBConfig, logger ? : WyclifLogger) {
        this.dbConfig = dbConfig
        this.logger = logger
    }

    /** Returns the singleton instance of the MongoManager */
    public static getInstance(dbConfig?: DBConfig, logger?: WyclifLogger): MongoAnalyticsService {
        if (!this.singletonInstance && dbConfig) {
            this.singletonInstance = new MongoAnalyticsService(dbConfig, logger);
        } 
        else if (!this.singletonInstance && (!dbConfig)) {
            throw new Error('No mongo manager available and no creation parameters supplied')
        }

        return this.singletonInstance
    }

    connectToMongoDb() {
        let url: string = `mongodb://${this.dbConfig.host}:${this.dbConfig.port}/?replicaSet=rs0`
        // this.logger.verbose('Mongo:', this.host, url)

        this.mongoClient = new MongoClient(url)
        this.mongoClient.connect((err, client) => {
            if (err) {
                // this.logger.error('unable to connect mongo reporting service to mongo:', err?.stack)
                return
            }

            if (client == undefined) {
                // this.logger.error('mongo client is undefined in mongo reporting service')
                return
            }

            // this.logger.verbose("Connected analytics to mongo!")

            this.dbConnection = client.db(this.dbConfig.database)

            this.analyticsCollection = this.dbConnection.collection('analytics')
            
            this.logger.trace('Connected to doc DB')
        }
    }
    
    addLift(lift: Lift): void {
        this.mongoClient.addtoCollection(this.analyticsCollection, lift);
    }
    
    addServer(server: Server): void {
        this.mongoClient.addtoCollection(this.analyticsCollection, server);
    }

    updateAccount(account: Account, serverId: number): void {
        //somehow we need to make sure the key for the account is the serverId
        this.mongoClient.addtoCollection(this.analyticsCollection, account)
    }
    
    updateBalance(balance: number, serverId: number): void {
        //somehow we need to make sure the key for the balance is the serverId
        this.mongoClient.addtoCollection(this.analyticsCollection, balance)
    }

}

export default MongoAnalyticsService
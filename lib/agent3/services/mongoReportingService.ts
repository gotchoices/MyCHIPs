import Account from "../account";
import Lift from "../models/Lift";
import Server from "../models/Server";
import ReportingServiceInterface from "./reportingServiceInterface"

// mongo
import * as mongoDB from "mongodb";
import * as dotenv from "dotenv";

//We need to create a .env and link to our own mongodb or find out where Kyle's is for his mongodb
//set DB_CONN_STRING
//set REPORTING_COLLECTION_NAME

export const collections: { reporting?: mongoDB.Collection } = {}

export async function connectToDatabase () {
    dotenv.config();
 
    const client: mongoDB.MongoClient = new mongoDB.MongoClient(process.env.DB_CONN_STRING);
            
    await client.connect();
        
    const db: mongoDB.Db = client.db(process.env.DB_NAME);
   
    const reportingCollection: mongoDB.Collection = db.collection(process.env.REPORTING_COLLECTION_NAME);
 
    collections.reporting = reportingCollection;
    
    console.log(`Successfully connected to database: ${db.databaseName} and collection: ${reportingCollection.collectionName}`);
}

class MongoReportingService implements ReportingServiceInterface {
    
    addLift(lift: Lift): void {
        throw new Error("Method not implemented.");
    }
    
    addServer(server: Server): void {
        throw new Error("Method not implemented.");
    }

    updateAccount(account: Account, serverId: number): void {
        throw new Error("Method not implemented.");
    }
    
    updateBalance(balance: number, serverId: number): void {
        throw new Error("Method not implemented.");
    }

}

export default MongoReportingService
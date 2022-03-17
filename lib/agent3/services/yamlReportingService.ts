import Account from "../account";
import Lift from "../models/Lift";
import Server from "../models/Server";
import ReportingServiceInterface from "./reportingServiceInterface";
import YAML from 'yaml'

class YamlReportingService implements ReportingServiceInterface{
    private static singletonInstance: YamlReportingService
    private lifts: Lift[]
    private servers: Server[]
    // Should this track numRuns?

    public static getInstance() {
        if (!YamlReportingService.singletonInstance ) {
          YamlReportingService.singletonInstance = new YamlReportingService;
        }
    
        return YamlReportingService.singletonInstance
    }

    public addLift(lift: Lift): void {
        this.lifts.push(lift)
    }

    public addServer(server: Server): void {
        this.servers.push(server)
    }

    public updateAccount(account: Account, serverId: number): void {
        this.servers.forEach(server => {
            if (server.id = serverId) {
                const accountIndex = server.accounts.findIndex((serverAccount) => serverAccount.id = account.id)
                if (accountIndex > -1) {
                    server.accounts[accountIndex] = account
                } 
                else {
                    server.accounts.push(account)
                }
            }
        });
    }

    public updateBalance(balance: number, serverId: number): void {
        this.servers.forEach(server => {
            if (server.id = serverId) {
                server.balance = balance
            }
        });
    }

    // All these methods would allow local data storage and we could simply write to a yaml at the end
    public writeOutput() {
        let outputString: string = this.lifts.toString() + this.servers.toString()
        YAML.stringify(outputString)
        //TODO write this to a reporting.yaml file
    }

}

export default YamlReportingService
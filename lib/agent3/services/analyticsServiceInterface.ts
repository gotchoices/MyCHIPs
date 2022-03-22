import Account from "../account"
import Lift from "../models/Lift"
import Server from "../models/Server"

interface ReportingServiceInterface {
    addLift(lift: Lift): void

    addServer(server: Server): void

    updateAccount(account: Account, serverId: number): void

    updateBalance(balance: number, serverId: number): void
}

export default ReportingServiceInterface
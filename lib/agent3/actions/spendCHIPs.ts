import Action from "../action";
import Account from "../account";
import AccountCache from "../accountsCache";
import MongoManager from "../mongomanager";
import SQLManager from "../sqlmanager";
import UnifiedLogger from "../unifiedLogger";

class SpendCHIPs implements Action {
    logger: WyclifLogger;
    myChipsDBManager: SQLManager;
    worldDBManager: MongoManager;
    accountCache: AccountCache;

    account: Account;
    
    constructor(account: Account) {
        this.logger = UnifiedLogger.getInstance()
        this.myChipsDBManager = SQLManager.getInstance()
        this.worldDBManager = MongoManager.getInstance()
        this.accountCache = AccountCache.getInstance()

        this.account = account
    }
    

    run(): void {
        if (this.account.numSpendingTargets > 0 && this.account.netWorth > this.account.minWorthToSpend) {
            console.log(this.account.peer_cid, "is spending some CHIPs")
            let chipsToSpend = Math.floor(Math.random() * Math.max(this.account.netWorth * this.account.maxToSpend, 1000))

            let peerToPayID = this.account.spendingTargets[Math.floor(Math.random() * this.account.numSpendingTargets)]
            console.log("\tAccount to pay:", peerToPayID)
            console.log("\tAmount to pay:", chipsToSpend)

            let peerToPay = this.accountCache.getAccount(peerToPayID)

            let sequence: number = this.account.foil_seqs[peerToPayID]

            this.myChipsDBManager.addPayment(this.account.id, peerToPay.id, chipsToSpend, sequence)
        }
    }

}

export default SpendCHIPs;
import Action from "../action";
import Account from "../account";
import AccountCache from "../accountsCache";
import MongoManager from "../mongomanager";
import SQLManager from "../sqlmanager";
import UnifiedLogger from "../unifiedLogger";

class FindNewSpendingTarget implements Action{
    logger: WyclifLogger
    myChipsDBManager: SQLManager
    worldDBManager: MongoManager
    accountCache: AccountCache

    account: Account
    
    constructor(account: Account) {
        this.logger = UnifiedLogger.getInstance()
        this.myChipsDBManager = SQLManager.getInstance()
        this.worldDBManager = MongoManager.getInstance()
        this.accountCache = AccountCache.getInstance()

        this.account = account
    }

    run() {        
        if (this.account.numSpendingTargets <= 0 ||                 // If the account has no stocks   or
            (this.account.numSpendingTargets < this.account.maxSpendingTargets &&   // (if the account doesn't have too many stocks and
              Math.random() < this.account.newSpendingTargetOdds))       //  we randgomly choose to))
        {
            this.worldDBManager.findPeerAndUpdate(this.account.peer_cid, this.account.spendingTargets, (newPeer: AccountData) => {
                console.log(newPeer)

                this.logger.debug(this.account.peer_cid, "  attempting new spending source with", newPeer.peer_cid)

                // Save new peer data locally
                if (!this.accountCache.containsAccount(newPeer)) {
                    this.myChipsDBManager.addAccount(newPeer)
                    this.accountCache.addAccount(newPeer)
                }
                
                // Request that the other server puts our data into their database
                let newPeerServer = newPeer.peer_socket.split(':')[0]
                this.worldDBManager.insertAction("createAccount", undefined, newPeerServer, () => {
                    this.myChipsDBManager.addConnectionRequest(this.account.id, newPeer.id)
                    // TODO: This stuff should only be done when the connection is accepted by the peer. Right now the peers always accept requests, so we can do it here. I'm not sure how we will get notified when the connection is accepted...
                    this.account.numSpendingTargets++
                    this.worldDBManager.updateOneAccount(this.account.getAccountData())
                })
            })
        }
    }
}

export default FindNewSpendingTarget;
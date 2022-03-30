import Action from '../action'
import Account from '../account'
import AccountCache from '../accountsCache'
import MongoManager from '../mongoWorldManager'
import SQLManager from '../sqlmanager'
import UnifiedLogger from '../unifiedLogger'

class FindNewIncomeSource implements Action {
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
    if (
      this.account.numIncomeSources <= 0 ||
      (this.account.numIncomeSources < this.account.maxIncomeSources &&
        Math.random() < this.account.newIncomeSourceOdds)
    ) {
      this.worldDBManager.findPeerAndUpdate(
        this.account.peer_cid,
        this.account.incomeSources,
        (newPeer: AccountData) => {
          this.logger.debug(
            this.account.peer_cid,
            ' attempting new income source with ',
            newPeer.peer_cid
          )

          if (!this.accountCache.containsAccount(newPeer)) {
            this.myChipsDBManager.addPeerAccount(newPeer)
            this.accountCache.addAccount(newPeer)
          }

          let newPeerServer = newPeer.peer_sock.split(':')[0]
          this.worldDBManager.insertAction(
            'createAccount',
            undefined,
            newPeerServer,
            () => {
              this.myChipsDBManager.addConnectionRequest(
                this.account.id,
                newPeer.id
              )
              // TODO: This stuff should only be done when the connection is accepted by the peer. Right now the peers always accept requests, so we can do it here. I'm not sure how we will get notified when the connection is accepted...
              this.account.numIncomeSources++
              this.worldDBManager.updateOneAccount(
                this.account.getAccountData()
              )
            }
          )
        }
      )
    }
  }
}

export default FindNewIncomeSource

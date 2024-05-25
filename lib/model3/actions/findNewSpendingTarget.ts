import Action from '../action'
import Account from '../account'
import MongoManager from '../mongoWorldManager'
import SQLManager from '../sqlmanager'
import UnifiedLogger from '../unifiedLogger'

class FindNewSpendingTarget implements Action {
  logger: WyclifLogger
  myChipsDBManager: SQLManager
  worldDBManager: MongoManager
  account: Account

  constructor(account: Account) {
    this.logger = UnifiedLogger.getInstance()
    this.myChipsDBManager = SQLManager.getInstance()
    this.worldDBManager = MongoManager.getInstance()
    this.account = account
  }

  // 1. Find peer in world DB (mongo)
  // 2. Send the Connection Request
  run() {
    if (
      this.account.numSpendingTargets <= 0 || // If the account has no stocks   or
      (this.account.numSpendingTargets < this.account.maxSpendingTargets && // (if the account doesn't have too many stocks and
        Math.random() < this.account.newSpendingTargetOdds)
    ) {
      //  we randomly choose to))
      this.logger.debug(`${this.account.peer_cuid} is finding a new spending target!`)
      this.worldDBManager.findPeerAndUpdate(
        this.account.peer_cuid,
        this.account.spendingTargetCids,
        (newPeer: AccountData) => {
          this.logger.debug(
            this.account.peer_cuid,
            '  attempting new spending source with',
            newPeer.peer_cuid
          )

          this.myChipsDBManager.addConnectionRequest(
            this.account.id,
            this.account.certificate,
            newPeer.cert
          )
        }
      )
    }
  }
}

export default FindNewSpendingTarget

import Action from '../action'
import Account from '../account'
import MongoManager from '../mongoWorldManager'
import SQLManager from '../sqlmanager'
import UnifiedLogger from '../unifiedLogger'

//TODO: This class is borken! Fix it using FindNewSpendingTarget as a template.
class FindNewIncomeSource implements Action {
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
        }
      )
    }
  }
}

export default FindNewIncomeSource

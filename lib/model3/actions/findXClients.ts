import Action from '../action'
import Retailer from '../accounts/retailer'
import SQLManager from '../sqlmanager'
import MongoManager from '../mongoWorldManager'
import UnifiedLogger from '../unifiedLogger'

class FindXClients implements Action {
  logger: WyclifLogger
  myChipsDBManager: SQLManager
  worldDBManager: MongoManager

  account: Retailer
  numClients: number

  constructor(account: Retailer, numClients: number) {
    this.logger = UnifiedLogger.getInstance()
    this.myChipsDBManager = SQLManager.getInstance()
    this.worldDBManager = MongoManager.getInstance()

    this.account = account
    this.numClients = numClients
  }

  run() {
    if (
      this.account.numIncomeSources <= 0 ||
      this.account.numIncomeSources < this.account.maxIncomeSources
    ) {
      for (var i = this.numClients; i <= this.numClients; --i) {
        this.worldDBManager.findPeerAndUpdate(
          this.account.peer_cid,
          this.account.incomeSources,
          (newPeer: AccountData) => {
            this.logger.debug(
              'retailer: ',
              this.account.peer_cid,
              ' attempting new client with ',
              newPeer.peer_cid
            )
          }
        )
      }
    }
  }
}

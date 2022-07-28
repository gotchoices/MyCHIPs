import Action from '../action'
import Account from '../account'
import MongoManager from '../mongoWorldManager'
import SQLManager from '../sqlmanager'
import UnifiedLogger from '../unifiedLogger'

class SpendCHIPs implements Action {
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

  run(): void {
    if (
      this.account.numSpendingTargets > 0 &&
      this.account.netWorth > this.account.minWorthToSpend
    ) {
      this.logger.debug(this.account.peer_cid, 'is sending CHIPs')
      let chipsToSpend = Math.floor(
        Math.random() *
          Math.max(this.account.netWorth * this.account.maxToSpend, 1000)
      )

      let peerIndex = Math.floor(
        Math.random() * this.account.numSpendingTargets
      )
      this.logger.trace('index:', peerIndex)
      this.logger.trace('ids:', this.account.spendingTargets)
      this.logger.trace('cids:', this.account.spendingTargetCids)

      let peerToPayID = this.account.spendingTargets[peerIndex]
      let peerToPayCID = this.account.spendingTargetCids[peerIndex]

      this.logger.trace('\tAccount to pay:', peerToPayCID)
      this.logger.trace('\tAmount to pay:', chipsToSpend)

      let sequence: number = this.account.foilSequenceNums[peerIndex]

      this.logger.trace('\tFoil sequence:', sequence)

      this.myChipsDBManager.addPayment(
        this.account.id,
        peerToPayID,
        chipsToSpend,
        sequence
      )
    }
  }
}

export default SpendCHIPs

import Action from '../action'
import Account from '../account'
import AccountCache from '../accountsCache'
import MongoManager from '../mongoWorldManager'
import SQLManager from '../sqlmanager'
import UnifiedLogger from '../unifiedLogger'

class SpendCHIPs implements Action {
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

  run(): void {
    if (
      this.account.numSpendingTargets > 0 &&
      this.account.netWorth > this.account.minWorthToSpend
    ) {
      console.log(this.account.peer_cid, 'is spending some CHIPs')
      let chipsToSpend = Math.floor(
        Math.random() *
          Math.max(this.account.netWorth * this.account.maxToSpend, 1000)
      )

      let peerIndex = Math.floor(
        Math.random() * this.account.numSpendingTargets
      )
      console.log('index:', peerIndex)
      console.log('ids:', this.account.spendingTargets)
      console.log('cids:', this.account.spendingTargetCids)

      let peerToPayID = this.account.spendingTargets[peerIndex]
      let peerToPayCID = this.account.spendingTargetCids[peerIndex]

      console.log('\tAccount to pay:', peerToPayCID)
      console.log('\tAmount to pay:', chipsToSpend)

      let sequence: number = this.account.foil_seqs[peerIndex]

      console.log('\tFoil sequence:', sequence)

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

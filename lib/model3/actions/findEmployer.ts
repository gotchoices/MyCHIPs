import Action from '../action'
import Retailer from '../accounts/retailer'
import SQLManager from '../sqlmanager'
import MongoManager from '../mongoWorldManager'
import UnifiedLogger from '../unifiedLogger'
import Employee from '../accounts/employee'
import FindNewIncomeSource from './findNewIncomeSource'
import BaseAccount from '../accounts/baseAccount'
import SpendCHIPs from './spendCHIPs'

class FindEmployer implements Action {
  logger: WyclifLogger
  myChipsDBManager: SQLManager
  worldDBManager: MongoManager

  account: Employee
  numClients: number

  constructor(account: Employee, numClients: number) {
    this.logger = UnifiedLogger.getInstance()
    this.myChipsDBManager = SQLManager.getInstance()
    this.worldDBManager = MongoManager.getInstance()

    this.account = account
    this.numClients = numClients
  }

  run() {
    this.worldDBManager.findPeerAndUpdate(
      this.account.peer_cid,
      this.account.incomeSources,
      (newPeer: AccountData) => {
        this.logger.debug(
          'employee: ',
          this.account.peer_cid,
          ' attempting new employer with ',
          newPeer.peer_cid
        )
        this.account.changeEmployer(
          new BaseAccount(newPeer, newPeer.peer_host, undefined)
        )
      }
    )

    //Request chips based on sallary from new employer
  }
}

export default FindEmployer

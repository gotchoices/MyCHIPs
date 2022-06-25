import Action from '../action'
import Account from '../account'
import SQLManager from '../sqlmanager'
import UnifiedLogger from '../unifiedLogger'

class AskForLift implements Action {
  logger: WyclifLogger
  myChipsDBManager: SQLManager
  account: Account

  constructor(account: Account) {
    this.logger = UnifiedLogger.getInstance()
    this.myChipsDBManager = SQLManager.getInstance()
    this.account = account
  }

  run(): void {
    //TODO: figure out how to get value from individual connections
    let greatestTallyValue = 20 // this is less than the default value, so this will never happen right now...
    if (greatestTallyValue > this.account.diffForLift) {
      this.logger.trace(this.account.peer_cid, 'is asking for a lift!')

      this.myChipsDBManager.requestLift(this.account.peer_cid)
    }
  }
}

export default AskForLift

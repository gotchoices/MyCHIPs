import Action from "../action";
import Account from "../account";
import AccountCache from "../accountsCache";
import MongoManager from "../mongomanager";
import SQLManager from "../sqlmanager";
import UnifiedLogger from "../unifiedLogger";

class AskForLift implements Action {
  logger: WyclifLogger;
  myChipsDBManager: SQLManager;
  account: Account;

  constructor(account: Account) {
    this.logger = UnifiedLogger.getInstance()
    this.myChipsDBManager = SQLManager.getInstance()
    this.account = account
  }

  run(): void {
    //TODO: figure out how to get value from individual connections
    let greatestTallyValue = 20
    if (greatestTallyValue > this.account.diffForLift) {
      console.log(this.account.peer_cid, "is asking for a lift!")
      
    }
  }
  
}
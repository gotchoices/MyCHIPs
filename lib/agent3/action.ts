import Account from './account'
import AccountCache from './accountsCache'
import MongoManager from './mongomanager'
import SQLManager from './sqlmanager'

interface Action {
  logger: WyclifLogger
  // I don't think all of these things are necessary for every action
  // myChipsDBManager: SQLManager
  // worldDBManager: MongoManager
  // accountCache: AccountCache

  run(): void
}

export default Action

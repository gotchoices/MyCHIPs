import Account from './account'
import AccountCache from './accountsCache'
import MongoManager from './mongoWorldManager'
import SQLManager from './sqlmanager'

interface Action {
  logger: WyclifLogger
  myChipsDBManager: SQLManager
  worldDBManager: MongoManager
  accountCache: AccountCache

  run(): void
}

export default Action

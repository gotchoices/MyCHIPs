import MongoManager from './mongoWorldManager'
import SQLManager from './sqlmanager'

interface Action {
  logger: WyclifLogger
  // I don't think these are necessary for every action
  // myChipsDBManager: SQLManager
  // worldDBManager: MongoManager

  run(): void
}

export default Action

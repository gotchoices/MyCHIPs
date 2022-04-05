import MongoManager from './mongoWorldManager'
import SQLManager from './sqlmanager'

interface Action {
  logger: WyclifLogger
  myChipsDBManager: SQLManager
  worldDBManager: MongoManager

  run(): void
}

export default Action

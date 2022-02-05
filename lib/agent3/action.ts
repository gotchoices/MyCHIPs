import Agent from "./agent";
import AgentsCache from "./agentsCache";
import MongoManager from "./mongomanager";
import SQLManager from "./sqlmanager";

interface Action {
    logger: WyclifLogger
    myChipsDBManager: SQLManager
    worldDBManager: MongoManager
    agentCache: AgentsCache

    run(): void
}

export default Action
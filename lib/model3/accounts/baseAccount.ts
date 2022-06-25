// import { WyclifLogger } from '../../@types/global'
import Action from '../action'
import Account from '../account'
import MongoManager from '../mongoWorldManager'
import SQLManager from '../sqlmanager'
import ActionFactory from '../actionFactory'
import UnifiedLogger from '../unifiedLogger'

class BaseAccount implements Account {
  id: string
  std_name: string
  ent_name: string
  first_name: string
  peer_cid: any
  agent: string
  certificate: certificate
  host: string
  port: number
  entity_type: string
  random: number
  actions: Action[]
  satisfied: boolean

  numSpendingTargets: number
  spendingTargets: string[]
  spendingTargetCids: string[]
  foilSequenceNums: number[]
  spendingTargetAgents: string[]

  numIncomeSources: number
  incomeSources: string[]
  incomeSourceCids: string[]
  stockSequenceNums: any[]
  incomeSourceAgents: string[]

  partnerCids: string[]
  targets: string[]
  sequenceNums: number[]
  tallyTypes: any[]
  netWorth: number

  newIncomeSourceOdds: number
  adjustSettingsOdds: number
  newSpendingTargetOdds: number
  maxSpendingTargets: number
  desiredSpendingTargets: number
  maxIncomeSources: number
  desiredIncomeSources: number
  minWorthToSpend: number
  maxToSpend: number
  diffForLift: number
  minForSatisfaction: number

  worldDBManager: MongoManager
  myChipsDBManager: SQLManager
  logger: WyclifLogger

  constructor(
    accountData: AccountData,
    host: string,
    accountParams?: AdjustableAccountParams
  ) {
    this.worldDBManager = MongoManager.getInstance()
    this.myChipsDBManager = SQLManager.getInstance()
    this.logger = UnifiedLogger.getInstance()
    this.logger.trace('Creating account object for', accountData.std_name)

    //TODO these need to have actual parameters for the factory
    this.actions = []
    this.actions.push(ActionFactory.createAction('NewSpendingSource', this))
    // this.actions.push(ActionFactory.createAction('NewIncomeSource', this)); // Not correctly implemented yet
    this.actions.push(ActionFactory.createAction('SpendCHIPs', this))
    this.actions.push(ActionFactory.createAction('AskForLift', this))

    this.id = accountData.id
    this.std_name = accountData.std_name
    this.ent_name = accountData.ent_name
    this.first_name = accountData.fir_name
    this.peer_cid = accountData.peer_cid
    this.agent = accountData.peer_agent
    this.certificate = accountData.cert
    this.host = accountData.peer_host || host
    this.port = accountData.peer_port
    this.entity_type = accountData.ent_type || 'p'
    this.random = Math.random()
    this.satisfied = false

    this.numSpendingTargets = accountData.foils || 0
    this.foilSequenceNums = accountData.foil_seqs || []
    this.spendingTargets = accountData.vendors || []
    this.spendingTargetCids = accountData.vendor_cids || []
    this.spendingTargetAgents = accountData.vendor_agents || []

    this.numIncomeSources = accountData.stocks || 0
    this.stockSequenceNums = accountData.stock_seqs || []
    this.incomeSources = accountData.clients || []
    this.incomeSourceCids = accountData.client_cids || []
    this.incomeSourceAgents = accountData.client_agents || []

    this.partnerCids = accountData.part_cids || []
    this.targets = accountData.targets || []
    this.sequenceNums = accountData.seqs || []
    this.tallyTypes = accountData.types || []
    this.netWorth = +accountData.net || 0

    this.newIncomeSourceOdds = accountParams?.newIncomeSourceOdds || 0.1
    this.adjustSettingsOdds = accountParams?.adjustSettingsOdds || 0.5
    this.newSpendingTargetOdds = accountParams?.newSpendingTargetOdds || 0.15
    this.maxSpendingTargets = accountParams?.maxSpendingTargets || 2
    this.desiredSpendingTargets = accountParams?.desiredSpendingTargets || 2
    this.maxIncomeSources = accountParams?.maxIncomeSources || 3
    this.desiredIncomeSources = accountParams?.desiredIncomeSources || 1
    this.minWorthToSpend = accountParams?.minWorthToSpend || -10000
    this.maxToSpend = accountParams?.maxToSpend || 0.1
    this.diffForLift = accountParams?.diffForLift || 30
    this.minForSatisfaction = accountParams?.minForSatisfaction || 5
  }

  takeAction(): void {
    // For now, I'm just having the Account perform all of its Actions. Since there's a percentage
    // associated with each Action that determines how likely it is to actually happen, I think
    // this is ok.
    this.actions.forEach((action) => {
      action.run()
    })

    this.calculateSatisfaction()
  }

  acceptNewConnection(message: any) {
    // I don't know how to tell the difference between types of connections (whether this account is the income source or spending target)
    // As a default Account, we will always accept a connection
    this.logger.debug(this.peer_cid, 'is accepting a connection request!')
    this.myChipsDBManager.updateConnectionRequest(
      message.entity,
      message.sequence,
      true
    )

    // TODO: update data here (depends on what kind of connection it is though...)
  }

  calculateSatisfaction(): void {
    if (
      this.numSpendingTargets >= this.desiredSpendingTargets &&
      this.numIncomeSources >= this.desiredIncomeSources &&
      this.netWorth >= this.minForSatisfaction
    ) {
      this.satisfied = true
    } else this.satisfied = false
  }

  updateAccountData(accountData: AccountData): void {
    this.logger.trace(this.peer_cid, 'is getting updated info')
    this.id = accountData.id
    this.std_name = accountData.std_name
    this.ent_name = accountData.ent_name
    this.first_name = accountData.fir_name
    this.peer_cid = accountData.peer_cid
    this.agent = accountData.peer_agent
    this.certificate = accountData.cert
    this.host = accountData.peer_host
    this.port = accountData.peer_port
    this.entity_type = accountData.ent_type
    this.random = Math.random()

    this.numSpendingTargets = accountData.foils
    this.spendingTargets = accountData.vendors
    this.spendingTargetCids = accountData.vendor_cids || []
    this.foilSequenceNums = accountData.foil_seqs
    this.spendingTargetAgents = accountData.vendor_agents || []

    this.numIncomeSources = accountData.stocks
    this.incomeSources = accountData.clients
    this.incomeSourceCids = accountData.client_cids || []
    this.stockSequenceNums = accountData.stock_seqs
    this.incomeSourceAgents = accountData.client_agents || []

    this.partnerCids = accountData.part_cids
    this.targets = accountData.targets || []
    this.sequenceNums = accountData.seqs
    this.tallyTypes = accountData.types || []
    this.netWorth = +accountData.net
  }

  getAccountData(): AccountData {
    return {
      id: this.id,
      std_name: this.std_name,
      ent_name: this.ent_name,
      fir_name: this.first_name,
      ent_type: this.entity_type,
      user_ent: this.id,
      peer_cid: this.peer_cid,
      peer_host: this.host,
      peer_agent: this.agent,
      peer_port: this.port,
      cert: this.certificate,
      random: this.random,

      stocks: this.numIncomeSources,
      clients: this.incomeSources,
      client_cids: this.incomeSourceCids,
      stock_seqs: this.stockSequenceNums,
      client_agents: this.incomeSourceAgents,

      foils: this.numSpendingTargets,
      vendors: this.spendingTargets,
      vendor_cids: this.spendingTargetCids,
      foil_seqs: this.foilSequenceNums,
      vendor_agents: this.spendingTargetAgents,

      part_cids: this.partnerCids,
      targets: this.targets,
      types: this.tallyTypes,
      net: this.netWorth,
      seqs: this.sequenceNums,
    }
  }

  getAccountAnalytics(): AccountAnalytics {
    this.calculateSatisfaction()
    return {
      name: this.std_name,
      peer_cid: this.peer_cid,
      id: this.id,
      stocks: this.numIncomeSources,
      foils: this.numSpendingTargets,
      netWorth: this.netWorth,
      satisfied: this.satisfied,
    }
  }
}

export default BaseAccount

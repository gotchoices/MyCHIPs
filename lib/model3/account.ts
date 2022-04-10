import Action from './action'

interface Account {
  //TODO add typing to these and figure out what they all do
  id: string
  /** Name of the entity */
  std_name: string
  /** Globally unique ID */
  peer_cid: any
  /** ID of the hosting server */
  host: string
  /** Something new that helps uniquely identify an account */
  agent: string
  /** The port this agent can be found on */
  port: number
  /** Something new that helps uniquely identify an account */
  certificate: certificate
  /** The type of entity */
  entity_type: string
  /** List of actions this entity can take */
  actions: Action[]
  /** Used to randomly sort agents in the world DB */
  random: number
  /** Describes whether the account is satisfied with its situation */
  satisfied: boolean

  /** The number of spending targets (foils) this entity holds */
  numSpendingTargets: number
  /** Other entities' IDs I hold the foil for (I give them money) aka Vendors*/
  spendingTargets: string[]
  /** Other entities' CIDs I hold the foil for */
  spendingTargetCids: string[]
  /** Sequence numbers for foils */
  foilSequenceNums: number[]
  /** List of agents for our spending targets */
  spendingTargetAgents: string[]

  /** The number of income sources (stocks) this entity holds */
  numIncomeSources: number
  /** Other entities' IDs I hold the stock for (they give me money) aka Clients */
  incomeSources: string[]
  /** Other entities' CIDs I hold the stock for */
  incomeSourceCids: string[]
  /** Sequence numbers for stocks */
  stockSequenceNums: number[]
  /** List of agents for our income sources */
  incomeSourceAgents: string[]

  /** Other entities' CIDs I have tallies with */
  partnerCids: string[]
  /** The types of each of my tallies ('stock' or 'foil') */
  tallyTypes: string[]
  /** Sequence numbers for all my tallies */
  sequenceNums: number[]
  /** Targets??? for my tallies */
  targets: string[]
  /** Net CHIPs owned by this account */
  netWorth: number

  /** A percentage defining how often this entity will try to add a new spending target (vendor or stock) */
  newSpendingTargetOdds: number
  /** A percentage defining how often this entity will try to add a new income source (client or foil) */
  newIncomeSourceOdds: number
  /** A percentage degining how often this entity will try to adjust its settings */
  adjustSettingsOdds: number
  /** The maximum number of spending targets (foils) this entity will open */
  maxSpendingTargets: number
  /** The minimum number of spending targets (foils) this account will need to be satisfied*/
  desiredSpendingTargets: number
  /** The maximum number of income sources (stocks) this entity will open */
  maxIncomeSources: number
  /** The minimum number of income sources (stocks) this account will need to be satisfied */
  desiredIncomeSources: number
  /** The minimum net worth the entity must have to be willing to spend money */
  minWorthToSpend: number
  /** A percentage defining the maximum amount this entity is willing to spend in one transaction */
  maxToSpend: number
  /** If the absolute value on any one connection (in or out) is greater than this, the account will ask for a lift */
  diffForLift: number
  /** If the net worth is less than this number, the account will not be satisfied */
  minForSatisfaction: number

  //take an action and update last action taken with class name
  //switch should take an action based on the number
  takeAction(): void

  /** Accepts a connection request for this account */
  acceptNewConnection(message: any): void

  updateAccountData(data: AccountData): void

  getAccountData(): AccountData

  calculateSatisfaction(): void

  getAccountAnalytics(): AccountAnalytics
}

export default Account

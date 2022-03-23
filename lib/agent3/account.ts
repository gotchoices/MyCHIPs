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
  /** Birthday of the user */
  birthday: string
  /** The type of entity */
  entity_type: string
  peer_socket: string
  /** The number of spending targets (foils) this entity holds */
  numSpendingTargets: number
  stock_seqs: number[]
  /** The number of income sources (stocks) this entity holds */
  numIncomeSources: number
  foil_seqs: number[]
  /** Net CHIPs owned by this account */
  netWorth: number
  /** Indicates whether the entity is hosted on this server or not (will we be representing non hosted entities?) */
  hosted_ent: boolean
  /** List of actions this entity can take */
  actions: Action[]
  lastActionTaken: string
  /** Other entities' IDs I hold the foil for (I give them money) aka Vendors*/
  spendingTargets: string[]
  /** Other entities' CIDs I hold the foil for */
  spendingTargetCids: string[]
  /** Other entities' IDs I hold the stock for (they give me money) aka Clients */
  incomeSources: string[]
  /** Other entities' CIDs I hold the stock for */
  incomeSourceCids: string[]
  types: any[]
  /** Used to randomly sort agents in the world DB */
  random: number

  /** A percentage defining how often this entity will try to add a new spending target (vendor or stock) */
  newSpendingTargetOdds: number
  /** A percentage defining how often this entity will try to add a new income source (client or foil) */
  newIncomeSourceOdds: number
  /** A percentage degining how often this entity will try to adjust its settings */
  adjustSettingsOdds: number
  /** The maximum number of spending targets (stocks) this entity will open */
  maxSpendingTargets: number
  /** The maximum number of income sources (foils) this entity will open */
  maxIncomeSources: number
  /** The minimum net worth the entity must have to be willing to spend money */
  minWorthToSpend: number
  /** A percentage defining the maximum amount this entity is willing to spend in one transaction */
  maxToSpend: number

  //take an action and update last action taken with class name
  //switch should take an action based on the number
  takeAction(): void

  /** Accepts a connection request for this account */
  acceptNewConnection(message: any): void

  updateAccountData(data: AccountData): void

  getAccountData(): AccountData
}

export default Account

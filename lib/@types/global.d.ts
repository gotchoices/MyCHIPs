interface WyclifLogger {
  error(...args: any[]): void
  warn(...args: any[]): void
  info(...args: any[]): void
  debug(...args: any[]): void
  verbose(...args: any[]): void
  silly(...args: any[]): void
  trace(...args: any[]): void
}

interface DBConfig {
  host: string
  database: string
  user: string
  port: string | undefined
  log: WyclifLogger
}
interface DDConfig {
  host: string
  database: string
  port: string | undefined
}

/** Adjustable parameters that determine how the simulation is run. Gathered from paramConfig.yaml */
interface AdjustableSimParams {
  /** The interval between rounds in the simulation (in milliseconds) */
  interval: number
  /** The number of rounds between automatic lift checks */
  liftInterval: number
  /** A list account parameters */
  accountTypes: AdjustableAccountParams[]
}

/** Adjustable parameters that determine how an account should act. Gathered from paramConfig.yaml */
interface AdjustableAccountParams {
  /** The type of entity. The string should equal one of the implemented types of entities */
  type: string
  /** The percentage of total entities on this server that should be made this type */
  percentOfTotal: number
  /** A percentage defining how often this entity will try to add a new spending target (vendor or foil) */
  newSpendingTargetOdds: number | undefined
  /** A percentage defining how often this entity will try to add a new income source (client or stock) */
  newIncomeSourceOdds: number | undefined
  /** A percentage degining how often this entity will try to adjust its settings */
  adjustSettingsOdds: number | undefined
  /** The maximum number of spending targets (foils) this entity will open */
  maxSpendingTargets: number | undefined
  /** The minimum number of spending targets (foils) this account will need to be satisfied*/
  desiredSpendingTargets: number | undefined
  /** The maximum number of income sources (stocks) this entity will open */
  maxIncomeSources: number | undefined
  /** The minimum number of income sources (stocks) this account will need to be satisfied */
  desiredIncomeSources: number | undefined
  /** The minimum net worth the entity must have to be willing to spend money */
  minWorthToSpend: number | undefined
  /** A percentage defining the maximum amount this entity is willing to spend in one transaction */
  maxToSpend: number | undefined
  /** If the absolute value on any one connection (in or out) is greater than this, the account will ask for a lift */
  diffForLift: number | undefined
  /** If the net worth is less than this number, the account will not be satisfied */
  minForSatisfaction: number | undefined
}

interface ActionData {
  action: string
  tag: string
  host: string | undefined
  from: string
}

interface AccountData {
  id: string
  /** last name, first name*/
  std_name: string
  /** entity name (last name) */
  ent_name: string
  /** first name */
  fir_name: string
  /** Entity type */
  ent_type: string
  user_ent: string
  peer_cid: string
  peer_agent: string
  peer_host: string
  peer_port: number
  cert: certificate
  /** The number of stocks (income sources) that this account holds */
  stocks: number
  /** The number of foils (spending targets) that this account holds */
  foils: number
  /** List of account IDs that this account is connected to (combines the vendors and clients arrays) */
  part_cids: string[]
  /** List of account IDs that this account holds a foil for (I pay them money) */
  vendors: string[]
  /** List of account peer_cids that this account holds a foil for */
  vendor_cids?: string[]
  /** List of account agents that this account holds a foil for */
  vendor_agents?: string[]
  /** List of account IDs that this account holds a stock for (they pay me money) */
  clients: string[]
  /** List of account peer_cids that this account holds a stock for */
  client_cids?: string[]
  /** List of account agents that this account holds a foil for */
  client_agents?: string[]
  /** List of sequence numbers that correspond to chits/payments on stock tallies */
  stock_seqs: number[]
  /** List of sequence numbers that correspond to chits/payments on foil tallies */
  foil_seqs: number[]
  /** The net worth of this account */
  net: number | string
  /** An array of strings ('stock' and 'tally') that indicates what kind of tally corresponds to the index */
  types?: string[]
  /** List of sequence numbers that correspond to chits/payments on tallies (combines the stock_seqs and foil_seqs arrays) */
  seqs: number[]
  targets?: string[]
  random?: number
}

interface certificate {
  chad: {
    cid: string
    host: string
    port: number
    agent: string
  }
  data: string
  name: {
    first: string
    surname: string
  }
  type: string
  place: string | undefined
  public: string | undefined
  connect: string | undefined
  indentity: {
    birth: {
      date: string
    }
    state: {
      country: string
    }
  }
}

interface AccountAnalytics {
  name: string
  peer_cid: string
  id: string
  stocks: number
  foils: number
  netWorth: number
  satisfied: boolean
}

interface LiftAnalytics {
  server: string
  numLifts: string
  lifts: LiftData[]
}

interface LiftData {
  seq: string
  request: string
  status: string
  units: string
  path: string
  circular: string
}

/** Used when pulling data from SQL */
interface ParamData {
  name: string
  value: any
}

/** Network config values passed in from simulation */
interface NetworkConfig {
  _: any[]
  m: number
  model: number
// peerServer: string
// s: string
// 'peer-server': string
  runs: number
//  dbHost: string
//  H: string
  'db-host': string
  dbName: string
  D: string
  'db-name': string
// dbAdmin: string
// A: string
// 'db-admin': string
  dbUser: string
  U: string
  'db-user': string
  dbPort: number | undefined
  P: number | undefined
  'db-port': number | undefined
  ddHost: string
  h: string
  'dd-host': string
  ddName: string
  d: string
  'dd-name': string
// ddAdmin: string
  ddUser: string
  u: string
  'dd-user': string
  agent: string
  a: string
  'dd-admin': string
  ddPort: string
  p: string
  'dd-port': string
  interval: number
  i: number
  $0: string
  done: function
}

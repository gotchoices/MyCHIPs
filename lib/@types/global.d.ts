/** Kyle's custom logger that outputs data to simulation logging windows */
interface WyclifLogger {
  error(...args: string[] | unknown[]): void
  warn(...args: string[]): void
  info(...args: string[]): void
  debug(...args: any[]): void
  verbose(...args: string[] | number[]): void
  silly(...args: string[]): void
  trace(...args: any[]): void
}

interface DBConfig {
  host: string
  database: string
  user: string
  port: string | undefined
}

/** Adjustable parameters that determine how the simulation is run. Gathered from paramConfig.yaml */
interface AdjustableSimParams {
  /** The interval between rounds in the simulation (in milliseconds) */
  interval: number
  /** A list account parameters */
  accountTypes: AdjustableAccountParams[]
}

/** Adjustable parameters that determine how an account should act. Gathered from paramConfig.yaml */
interface AdjustableAccountParams {
  /** The type of entity. The string should equal one of the implemented types of entities */
  type: string
  /** The percentage of total entities on this server that should be made this type */
  percentOfTotal: number
  /** A percentage defining how often this entity will try to add a new spending target (vendor or stock) */
  newSpendingTargetOdds: number | undefined
  /** A percentage defining how often this entity will try to add a new income source (client or foil) */
  newIncomeSourceOdds: number | undefined
  /** A percentage degining how often this entity will try to adjust its settings */
  adjustSettingsOdds: number | undefined
  /** The maximum number of spending targets (stocks) this entity will open */
  maxSpendingTargets: number | undefined
  /** The maximum number of income sources (foils) this entity will open */
  maxIncomeSources: number | undefined
  /** The minimum net worth the entity must have to be willing to spend money */
  minWorthToSpend: number | undefined
  /** A percentage defining the maximum amount this entity is willing to spend in one transaction */
  maxToSpend: number | undefined
}

interface ActionData {
  action: string
  tag: string
  host: string | undefined
  from: string
}

interface AccountData {
  id: number
  /** last name, first name*/
  std_name: string
  /** entity name (last name) */
  ent_name: string
  /** first name */
  fir_name: string
  /** Entity type */
  ent_type: string
  user_ent: string
  hosted_ent?: boolean | null
  peer_cid: string
  /** Assigned peer socket (ex: 'peer2:65430') */
  peer_socket: string
  stocks: number
  foils: number
  partners: string[]
  vendors: string[]
  clients: string[]
  stock_seqs: number[]
  foil_seqs: number[]
  units: number
  types?: string[]
  seqs: number[]
  random?: number
  /** Name of hosting peer server (ex: 'peer0') */
  host?: string
  born_date?: string
  peer_host?: string
  peer_port?: string
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
  peerServer: string
  s: string
  'peer-server': string
  runs: number
  dbHost: string
  H: string
  'db-host': string
  dbName: string
  D: string
  'db-name': string
  dbAdmin: string
  A: string
  'db-admin': string
  dbPort: number | undefined
  P: number | undefined
  'db-port': number | undefined
  ddHost: string
  h: string
  'dd-host': string
  ddName: string
  d: string
  'dd-name': string
  ddAdmin: string
  a: string
  'dd-admin': string
  ddPort: string
  p: string
  'dd-port': string
  interval: number
  i: number
  $0: string
}

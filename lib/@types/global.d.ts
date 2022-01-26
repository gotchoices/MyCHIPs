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
  interval: number
  addclient: number
  checksets: number
  addvendor: number
  maxstocks: number
  maxfoils: number
  mintotpay: number
  maxtopay: number
  maxtarget: number
}

/** Unique peer id */
interface PeerCID {
  peer_cid: string
}

interface ActionData {
  action: string
  tag: string
  host: string | undefined
  from: string
}

interface AgentData {
  id: string
  /** last name, first name*/
  std_name: string
  /** entity name (last name) */
  ent_name: string
  /** first name */
  fir_name: string
  /** Entity type */
  ent_type: string
  user_ent: string | null
  peer_cid: PeerCID
  /** Assigned peer socket (ex: 'peer2:65430') */
  peer_sock: string
  stocks: number
  foils: number
  partners: string[]
  vendors: string[]
  clients: string[]
  vendor_cids: string[]
  client_cids: string[]
  stock_seqs: number[]
  foil_seqs: number[]
  units: string
  types: string[]
  seqs: number[]
  targets: string[]
  random?: number
  /** Name of hosting peer server (ex: 'peer0') */
  host?: string
  born_date?: string
  peer_host?: string
  peer_port?: string
}

/* Function Types */

type CheckPeerFn = (
  peerData: AgentData,
  cb: (agentData: AgentData) => void
) => void

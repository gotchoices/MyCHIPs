import Account from '../../agent3/account'

export interface Lift {
  liftId: number
  totalAccounts: number
  success: boolean
}

export interface Server {
  id: string
  balance: number
  accounts: Account[]
  actualRuns: number // Actual number of simulation runs executed by this server
}

import Account from '../../agent3/account'

export interface Lift {
  liftId: number
  totalAccounts: number
  success: boolean
}

export interface Server {
  id: number
  balance: number
  accounts: Account[]
}

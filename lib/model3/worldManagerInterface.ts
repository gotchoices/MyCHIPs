import { Server, Lift } from '../@types/models'

interface WorldManagerInterface {
  createConnection(
    notifyOfNewAccountRequest: (
      accountData: AccountData,
      tag: string,
      destHost: string
    ) => void,
    loadInitialUsers: () => void
  ): void

  isDBClientConnected(): boolean

  // insertAction(accountId: string): void

  updateOneAccount(account: AccountData): void

  analyticsAddLift(lift: Lift): void

  analyticsAddServer(server: Server): void
}

export default WorldManagerInterface

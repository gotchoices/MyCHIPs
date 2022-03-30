import UnifiedLogger from './unifiedLogger'

class AccountCache {
  private static instance: AccountCache

  private accountCache: { [cid: string]: AccountData }
  private logger: WyclifLogger

  private constructor() {
    this.accountCache = {}
    this.logger = UnifiedLogger.getInstance()
  }

  public static getInstance(): AccountCache {
    if (!AccountCache.instance) {
      AccountCache.instance = new AccountCache()
    }
    return AccountCache.instance
  }

  public addAccount(accountData: AccountData) {
    this.accountCache[accountData.peer_cid] = accountData
  }

  // Check to see if a peer is in our system, if not add them and then do cb
  public containsAccount(targetAccount: AccountData): boolean {
    let foundAccountData = this.accountCache[targetAccount.peer_cid]

    this.logger.debug(
      'Checking if we have peer:',
      targetAccount.peer_cid,
      !!foundAccountData
    )
    if (foundAccountData) {
      this.logger.debug(
        'Found match for peer',
        targetAccount.peer_cid,
        'in system'
      )
      return true
    } else {
      this.logger.debug(
        'No match found for peer',
        targetAccount.peer_cid,
        '. Creating one now.'
      )
      return false
    }
  }

  public getAccountByCID(peer_cid: string): AccountData {
    let foundAccount = this.accountCache[peer_cid]
    if (foundAccount) {
      return foundAccount
    } else {
      console.log('\n\nError in the Account Cache!:\n', this.accountCache)
      throw 'No account with given peer_cid is found ' + peer_cid
    }
  }
}

export default AccountCache

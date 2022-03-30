import Account from './account'
import BaseAccount from './accounts/baseAccount'

class AccountFactory {
  public static createAccount(
    accountType: string,
    accountData: AccountData,
    host: string,
    parameters?: AdjustableAccountParams
  ): Account {
    var account

    if (accountType === 'BaseAccount' || accountType == 'default') {
      account = new BaseAccount(accountData, host, parameters)
    }
    // Add more types here...
    else {
      account = new BaseAccount(accountData, host)
    }

    return account
  }
}

export default AccountFactory

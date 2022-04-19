import BaseAccount from '../accounts/baseAccount'
import ActionFactory from '../actionFactory'

class Retailer extends BaseAccount {
  private minSale: number
  private maxSale: number

  constructor(
    minSale: number,
    maxSale: number,
    accountData: AccountData,
    host: string,
    accountParams?: AdjustableAccountParams
  ) {
    super(accountData, host, accountParams)

    this.minSale = minSale
    this.maxSale = maxSale

    //TODO these need to have actual parameters for the factory
    this.actions.push(ActionFactory.createAction('FindXClients', this))
  }
}

export default Retailer

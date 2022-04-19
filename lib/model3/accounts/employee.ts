import BaseAccount from './baseAccount'
import ActionFactory from '../actionFactory'
import Account from '../account'

class Employee extends BaseAccount {
  private minSpend: number
  private maxSpend: number
  private employer: Account
  private sallary: number

  constructor(
    minSpend: number,
    maxSpend: number,
    employer: Account,
    sallary: number,
    accountData: AccountData,
    host: string,
    accountParams?: AdjustableAccountParams
  ) {
    super(accountData, host, accountParams)

    this.minSpend = minSpend
    this.maxSpend = maxSpend
    this.employer = employer
    this.sallary = sallary

    //TODO these need to have actual parameters for the factory
    this.actions.push(ActionFactory.createAction('FindEmployer', this))
  }

  public changeEmployer(employer: Account) {
    this.sallary += this.sallary * 0.1
    this.employer = employer
  }
}

export default Employee

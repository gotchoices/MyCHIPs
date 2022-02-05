import Action from './action'

interface Agent {
    //TODO add typing to these and figure out what they all do
    id: number
    /** Name of the entity */
    std_name: string
    /** Globally unique ID */
    peer_cid: any 
    /** The number of spending targets (stocks) this entity holds */
    numSpendingTargets: number
    /** The number of income sources (foils) this entity holds */
    numIncomeSources: number
    foil_seq: any
    units: any
    /** Indicated whether the entity is hosted on this server or not (will we be representing non hosted entities?) */
    hosted_ent: boolean
    /** List of actions this entity can take */
    actions: Action[]
    lastActionTaken: string
    /** Other entities I hold the stock for (I give them money) aka Vendors*/
    spendingTargets: any[] 
    /** Other entities I hold the foil for (they give me money) aka Clients */
    incomeSources: any[]
    seqs: any[]
    types: any[] 

    /** A percentage defining how often this entity will try to add a new spending target (vendor or stock) */
    newSpendingTargetOdds: number
    /** A percentage defining how often this entity will try to add a new income source (client or foil) */
    newIncomeSourceOdds: number 
    /** A percentage degining how often this entity will try to adjust its settings */
    adjustSettingsOdds: number 
    /** The maximum number of spending targets (stocks) this entity will open */
    maxSpendingTargets: number
    /** The maximum number of income sources (foils) this entity will open */
    maxIncomeSources: number
    /** The minimum net worth the entity must have to be willing to spend money */
    minWorthToSpend: number
    /** A percentage defining the maximum amount this entity is willing to spend in one transaction */
    maxToSpend: number

    //take an action and update last action taken with class name
    //switch should take an action based on the number
    takeAction(): void

}

export default Agent
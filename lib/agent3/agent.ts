import Action from './action'

interface Agent {
    //TODO add typing to these and figure out what they all do
    id: number
    std_name: string
    peer_cid: any 
    stocks: any 
    foils: any
    foil_seq: any
    units: any
    maxToPay: any
    maxTargets: number
    user_ent: boolean
    actions: Action[]
    lastActionTaken: string
    targets: any[] 
    seqs: any[]
    types: any[] 

    //take an action and update last action taken with class name
    //switch should take an action based on the number
    takeAction(): void

}

export default Agent
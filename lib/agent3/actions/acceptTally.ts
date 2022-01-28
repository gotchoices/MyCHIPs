import Action from "../action";
import Agent from "../agent";

class AcceptTally implements Action{
    agent: Agent;
    parameters: any;
    checkForPeer: any;
    remoteCall: any;
    
    constructor(agent: Agent, parameters: any, checkForPeer: any, remoteCall: any) {
        this.agent = agent
        this.parameters = parameters
        this.checkForPeer = checkForPeer
        this.remoteCall = remoteCall
    }
    
    run(): void {
        throw new Error("Method not implemented.");
        // tallyState(message: any): void {
        //     //Someone is asking an agent to act on a tally
        //     this.logger.debug('Peer Message:', message)
    
        //     if (message.state == 'peerProffer') {
        //     //For now, we will just answer 'yes'
        //     this.logger.verbose('  peerProffer:', message.entity)
        //     this.myChipsDBManager.query(
        //         "update mychips.tallies_v set request = 'open' where tally_ent = $1 and tally_seq = $2",
        //         [message.entity, message.sequence],
        //         (e, r) => {
        //         if (e) {
        //             this.logger.error('In :', e.stack)
        //             return
        //         }
        //         //        let row = r.rows && r.rows.length >= 1 ? r.rows[0] : null
        //         //          , aData = this.agents.findIndex(el=>(el.peer_cid == row.peer_cid))
        //         this.logger.verbose('  Tally affirmed:', message.object)
        //         }
        //     )
        //     }
        // }
    }
}

export default AcceptTally;
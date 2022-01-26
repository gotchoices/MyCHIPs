import Action from "../action";
import Agent from "../agent";

class NewTally implements Action{
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
        //Try to request tally from someone in the world
        // this.logger.debug('  Try tally:', agentData.peer_cid, 'with', pDoc.peer_cid)
        // this.checkPeer(peer, (peerDoc) => {
        //     let host = pDoc.peer_socket.split(':')[0]
        //     console.log('peer: ', pDoc)
        //     console.log('host: ', host)
        // this.remoteCall(host, 'createUser', agentData, () => {
        //     //Insert this peer remotely
        //     let guid = uuidv4(),
        //     sig = 'Valid',
        //     contract = { name: 'mychips-0.99' },
        //     tallySql =
        //         'insert into mychips.tallies_v (tally_ent, tally_guid, partner, user_sig, contract, request) values ($1, $2, $3, $4, $5, $6);',
        //     partner = 'test'

        //     this.logger.debug('Tally request:', tallySql, agentData.id, pData.id)

        //     this.myChipsDBManager.query(
        //     tallySql,
        //     [agentData.id, guid, pData.id, sig, contract, 'draft'],
        //     (err, res) => {
        //         if (err) {
        //         this.logger.error('In query:', err.stack)
        //         return
        //         }
        //         this.logger.debug(
        //         '  Initial tally by:',
        //         agentData.std_name,
        //         ' with partner:',
        //         pData.std_name
        //         )
        //         agentData.stocks++
        //         //          pData.foils++
        //     }
        //     )
        // })
        // })
    }
}

export default NewTally;
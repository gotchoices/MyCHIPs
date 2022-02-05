"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
class PayVendor {
    constructor(agent, parameters, checkForPeer, remoteCall) {
        this.agent = agent;
        this.parameters = parameters;
        this.checkForPeer = checkForPeer;
        this.remoteCall = remoteCall;
    }
    run() {
        throw new Error("Method not implemented.");
        // payVendor(vendor: Agent): void {
        //     let guid = uuidv4();
        //     let sig = 'Valid';
        //     let max = Math.max(this.units * this.maxToPay, 1000); //Pay 1 CHIP or % of net worth
        //     let units = Math.floor(Math.random() * max);
        //     let seq = this.foil_seq[vendor.peer_cid]; //Tally sequence
        //     let quid = 'Inv' + Math.floor(Math.random() * 1000);
        //     let req = 'userDraft';
        //     let sql = "insert into mychips.chits_v (chit_ent,chit_seq,chit_guid,chit_type,signature,units,quidpro,request) values ($1,$2,$3,'tran',$4,$5,$6,$7)";
        //     this.logger.verbose('  payVendor:', this.id, '->', vendor.id, 'on:', seq, 'Units:', units);
        //     this.myChipsDBManager.query(
        //         sql,
        //         [this.id, seq, guid, sig, units, quid, req],
        //         (e, r) => {
        //             if (e) {
        //                 this.logger.error('In payment:', e.stack)
        //                 return
        //             }
        //             this.logger.debug('  payment:', this.id, this.std_name, 'to:', vendor.id, vendor.std_name)
        //         }
        //     );
        // }
    }
}
exports.default = PayVendor;

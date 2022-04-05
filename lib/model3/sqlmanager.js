"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
// const { dbClient } = require('wyseman')
const wyseman_1 = require("wyseman");
const unifiedLogger_1 = __importDefault(require("./unifiedLogger"));
const uuid_1 = require("uuid");
const userSql = `select id, std_name, ent_name, fir_name, ent_type, user_ent,
	peer_cid, peer_agent, peer_host, peer_port, mychips.user_cert(id) as cert, stocks, foils, part_cids, vendors, clients,
	vendor_cids, vendor_agents, client_cids, stock_seqs, foil_seqs, units, types, seqs, targets
	from mychips.users_v_tallysum
	where not user_ent isnull`;
const parmQuery = "select parm,value from base.parm_v where module = 'agent'";
class SQLManager {
    constructor(sqlConfig, params) {
        // These member variables are never used, but might be if we implement some of the other functions
        // private channels: string[] = []
        // private host: string
        // private database: string
        // private user: string
        // private port: string
        /** Used to make sure that users are only loaded once */
        this.loadingUsers = false;
        this.logger = unifiedLogger_1.default.getInstance();
        this.params = params;
        // Add fields to config
        this.config = Object.assign({
            log: this.logger,
            listen: ['parm_model', 'mychips_admin', 'mychips_user'],
        }, sqlConfig);
    }
    static getInstance(sqlConfig, params) {
        if (!SQLManager.singletonInstance && sqlConfig && params) {
            SQLManager.singletonInstance = new SQLManager(sqlConfig, params);
        }
        else if (!SQLManager && (!sqlConfig || !params)) {
            throw new Error('no singleton instance exists and no paramaters supplied for creation');
        }
        return SQLManager.singletonInstance;
    }
    createConnection(notifyOfAccountChange, notifyOfParamsChange, notifyOfTallyChange) {
        console.log('Connecting to MyCHIPs DB...');
        this.dbConnection = new wyseman_1.dbClient(this.config, (channel, payload) => {
            //Initialize Database connection
            let msg;
            this.logger.trace('Account DB async on:', channel, 'payload:', payload);
            if (payload)
                try {
                    msg = JSON.parse(payload);
                }
                catch (e) {
                    this.logger.error('Parsing json payload: ' + payload);
                }
            if (channel == 'parm_model') {
                //Parameter updated
                this.logger.debug('Parameter', msg.target, '=', msg.value, msg);
                if (msg.target in this.params && msg.value)
                    notifyOfParamsChange(msg.target, msg.value);
            }
            else if (channel == 'mychips_admin') {
                //Something in the user data has changed
                if (msg.target == 'peers' || msg.target == 'tallies') {
                    notifyOfAccountChange(msg);
                }
            }
            else if (channel == 'mychips_user') {
                //Another account is contacting us
                if (msg.target == 'tally') {
                    //Someone wants to make a tally with one of our accounts
                    notifyOfTallyChange(msg);
                }
            }
        });
        console.log('MyCHIPs DB Connected!');
        this.logger.info('SQL Connection Created');
    }
    addConnectionRequest(requestingAccountID, requestingAccountCertificate, targetAccountCertificate) {
        let uuid = (0, uuid_1.v4)();
        let sig = 'Valid';
        let contract = { name: 'mychips-0.99' };
        this.logger.debug('Tally request:', requestingAccountID, targetAccountCertificate);
        console.log('Making a connection/tally between', requestingAccountCertificate.chad.cid, 'and', targetAccountCertificate.chad.cid);
        this.query('insert into mychips.tallies_v (tally_ent, tally_uuid, contract, request, hold_cert, part_cert, hold_sig) values ($1, $2, $3, $4, $5, $6, $7);', [
            requestingAccountID,
            uuid,
            contract,
            'offer',
            requestingAccountCertificate,
            targetAccountCertificate,
            sig,
        ], (err, res) => {
            if (err) {
                this.logger.error('Inserting a tally:', err.stack);
                console.log('Error while making tally between', requestingAccountID, 'and', targetAccountCertificate);
                console.log(err);
                return;
            }
            this.logger.debug('  Initial tally by:', requestingAccountID, ' with partner:', targetAccountCertificate);
        });
    }
    updateConnectionRequest(entity, sequence, accepted) {
        if (accepted) {
            this.query("update mychips.tallies_v set request = 'open' where tally_ent = $1 and tally_seq = $2", [entity, sequence], (err, res) => {
                if (err) {
                    this.logger.error('Updating a Tally:', err.stack);
                }
            });
        }
        else {
            //TODO: figure out how to mark the tally as unaccepted (just delete it?)
        }
    }
    addPayment(spenderId, receiverId, chipsToSpend, sequence) {
        let quid = 'Inv' + Math.floor(Math.random() * 1000);
        this.logger.verbose('  payVendor:', spenderId, '->', receiverId, 'on:', sequence, 'Units:', chipsToSpend);
        this.query("insert into mychips.chits_v (chit_ent,chit_seq,chit_guid,chit_type,signature,units,quidpro,request) values ($1,$2,$3,'tran',$4,$5,$6,$7)", [spenderId, sequence, (0, uuid_1.v4)(), 'Valid', chipsToSpend, quid, 'userDraft'], (e, r) => {
            if (e) {
                this.logger.error('In payment:', e.stack);
                console.log('Error when', spenderId, 'tried to pay', receiverId, chipsToSpend, 'chips');
                return;
            }
            this.logger.debug('  payment:', spenderId, 'to:', receiverId);
        });
    }
    isActiveQuery() {
        return this.dbConnection.client.activeQuery != null;
    }
    closeConnection() {
        this.dbConnection.disconnect();
    }
    getParameters(callback) {
        this.query(parmQuery, (err, res) => {
            if (err) {
                this.logger.error('Getting parameters:', err.stack);
                return;
            }
            callback(res.rows);
        });
    }
    /**
     * Executes database query to get all initial acounts
     * @param callback: eatAccounts - loads queried accounts into the worldDB
     * */
    // ! TODO Does this fetch from all peers?
    // ! ANSWER No, just from the matching pg database/container
    queryAccounts(callback) {
        console.log('Getting users from MyCHIPs DB');
        this.query(userSql, (err, res) => {
            if (err) {
                this.logger.error('Getting Users:', err.stack);
                return;
            }
            this.logger.trace('Loaded accounts:', res.rows.length);
            callback(res.rows, true);
        });
    }
    queryLatestUsers(time, callback) {
        // Only load users once at time
        if (!this.loadingUsers) {
            this.loadingUsers = true;
            this.query(userSql + ' and latest >= $1', [time], (err, res) => {
                this.loadingUsers = false;
                if (err) {
                    this.logger.error('Getting latest Users:', err.stack);
                    return;
                }
                this.logger.trace('Loaded accounts:', res.rows.length);
                callback(res.rows);
            });
        }
        else {
            console.log("Tried to query users when I'm already doing that!");
        }
    }
    query(...args) {
        this.dbConnection.query(...args);
    }
}
exports.default = SQLManager;

"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
const sqlmanager_1 = __importDefault(require("./model3/sqlmanager"));
const mongoWorldManager_1 = __importDefault(require("./model3/mongoWorldManager"));
const os_1 = __importDefault(require("os"));
const unifiedLogger_1 = __importDefault(require("./model3/unifiedLogger"));
const accountFactory_1 = __importDefault(require("./model3/accountFactory"));
/**
 * @class AccountCluster
 * Each 'model' docker container runs an AccountCluster instance
which is in charge of managing the simulation for that container
 * Each AccountCluster instance has exclusive access to its corresponding MyChips database and shared access to the World database.
 * The World database is the means by which the AccountClusters communicate
 with eachother
 * The AccountCluster only has to worry about qualifying and initiating
 credit lifts. The actual heavy lifting occurs automatically within the pg and peers databases once a lift is initated by having the AccountCluster insert accounts into the pg containers.
 // TODO: ^ this is not true
 */
class AccountCluster {
    constructor(myChipsDBConfig, worldDBConfig, networkConfig) {
        console.log('STARTING MODEL * VERSION 3 *');
        this.networkConfig = networkConfig;
        this.host = os_1.default.hostname();
        this.agent = networkConfig.agent;
        console.log('SERVER:', this.host);
        console.log('AGENT:', this.agent);
        // Bind functions we are passing as callbacks (makes sure `this` always refers to this object)
        this.loadInitialUsers = this.loadInitialUsers.bind(this);
        this.notifyOfTallyChange = this.notifyOfTallyChange.bind(this);
        this.notifyOfAccountsChange = this.notifyOfAccountsChange.bind(this);
        this.eatAccounts = this.eatAccounts.bind(this);
        this.eatParameters = this.eatParameters.bind(this);
        this.process = this.process.bind(this);
        // Initialize account logger
        this.logger = unifiedLogger_1.default.getInstance();
        this.logger.info('Starting up Account Server v3 on:', this.host);
        // Start setting things up
        this.hostedAccounts = [];
        this.loadParamsConfig();
        this.configureDatabases(myChipsDBConfig, worldDBConfig);
        this.run();
    }
    // Loads parameters from the config file
    loadParamsConfig() {
        const fs = require('fs');
        const yaml = require('js-yaml');
        this.logger.debug('Loading parameters from config file');
        try {
            let fileContents = fs.readFileSync(__dirname + '/model3/paramConfig.yaml');
            this.params = yaml.load(fileContents);
            console.log(this.params);
        }
        catch (e) {
            console.log(e);
            this.logger.error(e);
        }
    }
    configureDatabases(myChipsDBConfig, worldDBConfig) {
        this.logger.debug('Configuring the databases');
        // Configure SQLManager
        this.myChipsDBManager = sqlmanager_1.default.getInstance(myChipsDBConfig, this.params);
        // Configure MongoManager
        this.worldDBManager = mongoWorldManager_1.default.getInstance(worldDBConfig, this.networkConfig);
    }
    // calls run on all of the accounts
    run() {
        this.runCounter = 0;
        if (this.networkConfig.runs) {
            this.runs = this.networkConfig.runs;
        } //Max iterations
        console.log('### RUNNING', this.runs, 'ROUNDS ###');
        this.myChipsDBManager.createConnection(this.notifyOfAccountsChange, this.notifyOfParamsChange, this.notifyOfTallyChange);
        this.intervalTimer = null;
        // TODO: determine if this is necessary with new paramConfig.yaml
        this.myChipsDBManager.getParameters(this.eatParameters);
        this.worldDBManager.createConnection(
        // loadInitialUsers is called once the connection is created asynchronously
        this.loadInitialUsers);
        //TODO: Right now we're in callback heck, despite our efforts to clean it up. I want to start
        // using the async/await syntax to get rid of all of the callbacks.
        // Because of this, the simulation doesn't start until eatAccounts() finishes running for the
        // first time.
    }
    startSimulationRound() {
        if (this.intervalTimer)
            clearInterval(this.intervalTimer); // Restart interval timer
        this.intervalTimer = setInterval(() => {
            // If there is no limit on runs, or we're below the limit...
            if (!this.runs || this.runCounter < this.runs) {
                ++this.runCounter;
                console.log('\n###RUN NUMBER', this.runCounter, '###');
                // Process each hosted account this round
                this.hostedAccounts.forEach(this.process);
                // If this round falls in the right interval, run some lifts automatically
                if (this.runCounter % this.params.liftInterval == 0) {
                    this.myChipsDBManager.performAutoLifts();
                }
            }
            else {
                // TODO: Add setTimeout() or otherwise handle asynchronous
                console.log(`END OF SIM ************* ${this.host} with ${this.runCounter} runs`);
                this.close();
                this.recordFinalAnalytics();
            }
        }, this.params.interval);
    }
    // --- Functions passed as callbacks -------------------------------------------------------
    /** Callback
     * Loads accounts from the MyCHIPs Database
     */
    loadInitialUsers() {
        this.logger.debug('Loading initial accounts');
        this.myChipsDBManager.queryAccounts(this.eatAccounts); //Load up initial set of users
    }
    // gets accounts from SQL, updates local info, and puts hosted account info into MongoDB
    notifyOfAccountsChange(message) {
        // console.log('Change in the accounts:\n', message)
        this.myChipsDBManager.queryLatestUsers(message.time, this.eatAccounts);
    }
    notifyOfParamsChange(target, value) {
        this.params[target] = value;
    }
    notifyOfTallyChange(message) {
        this.logger.debug('Peer Message:', message);
        // console.log('Change in a tally:', message)
        //Someone is asking an account to act on a tally
        if (message.state == 'P.offer') {
            this.logger.verbose('Tally offer:', message.entity);
            this.hostedAccounts.forEach((account) => {
                if (account.id == message.entity) {
                    account.acceptNewConnection(message);
                }
            });
        }
    }
    // --- Helper Functions --------------------------------------------------------
    // -----------------------------------------------------------------------------
    /** Callback
     * Takes the accounts from the MyChipsDBManager and loads them into the worldDB. Called whenever there is a change in the users table (postgres)
     *  @param dbAccounts - array of accounts fetched from MyChips Databases
     * * First time it's run dbAccounts (which contains postgres data) only has local data, on subsequence it has both local and world data, so it filters and only updates worldDB with local accounts
     * @param first - boolean that states whether this is the first time being run
     */
    eatAccounts(dbAccounts, first) {
        // Make sure document db is connected and ready
        if (!this.worldDBManager.isDBClientConnected()) {
            return;
        }
        console.log('\nAccounts updated:', dbAccounts.length);
        // If loading all users (loading for the first time)
        if (first) {
            console.log('Creating my account objects!');
            // Ensure all accounts hosted on this server have an Account object
            let typesToMake = [];
            this.params.accountTypes.forEach((accountType) => {
                for (let i = 0; i < Math.round(accountType.percentOfTotal * dbAccounts.length); i++) {
                    typesToMake.push([accountType.type, accountType]);
                }
            });
            for (let i = 0; i < dbAccounts.length - typesToMake.length; i++) {
                typesToMake.push(['default', undefined]);
            }
            let hostedAccountIds = [];
            for (let i = 0; i < dbAccounts.length; i++) {
                let newAccount = accountFactory_1.default.createAccount(typesToMake[i][0], dbAccounts[i], this.host, typesToMake[i][1]);
                this.worldDBManager.updateOneAccount(newAccount.getAccountData());
                this.hostedAccounts.push(newAccount);
                hostedAccountIds.push(newAccount.peer_cid);
            }
            // Start the simulation! It starts here because it can't start until the accounts are loaded and that happens here in a callback to an async method.
            this.startSimulationRound();
        }
        else {
            console.log('Updating my local accounts');
            dbAccounts.forEach((accountData) => {
                this.hostedAccounts.forEach((hostedAccount) => {
                    if (hostedAccount.peer_cid == accountData.peer_cid) {
                        console.log(`\n${accountData.peer_cid}`
                        // :\nkey:\t\t\t\told:\t\t\t\tnew:`
                        );
                        // Object.keys(accountData).forEach((key) => {
                        //   let oldVal = hostedAccount.getAccountData()[key]
                        //   let newVal = accountData[key]
                        //   if (Array.isArray(newVal)) {
                        //     console.log(`${key}:\t\t[${oldVal}],\t\t[${newVal}]`)
                        //   } else {
                        //     console.log(`${key}:\t\t${oldVal},\t\t${newVal}`)
                        //   }
                        // })
                        hostedAccount.updateAccountData(accountData);
                        this.worldDBManager.updateOneAccount(hostedAccount.getAccountData());
                    }
                });
            });
        }
    }
    // -----------------------------------------------------------------------------
    //Digest operating parameters from database
    eatParameters(parameters) {
        this.logger.trace('eatParams');
        parameters.forEach((parameter) => {
            let { name, value } = parameter;
            this.params[name] = value;
        });
    }
    // -----------------------------------------------------------------------------
    //Shut down this controller
    close() {
        this.logger.debug('Shutting down account handler');
        if (this.myChipsDBManager.isActiveQuery()) {
            //If there is a query in process
            setTimeout(this.close, 500); //Try again in a half second
        }
        else {
            this.myChipsDBManager.closeConnection();
        }
        if (this.intervalTimer)
            clearInterval(this.intervalTimer);
    }
    // -----------------------------------------------------------------------------
    process(account) {
        //Iterate on a single account
        // @ts-ignore
        this.logger.verbose('Handler', this.runCounter, account.id, account.std_name, account.peer_cid);
        console.log(account.peer_cid, 'is taking their turn');
        account.takeAction();
        this.logger.debug('  stocks:', account.numIncomeSources, '  foils:', account.numSpendingTargets);
    }
    recordFinalAnalytics() {
        const currServer = {
            id: this.host,
            balance: 0,
            accounts: this.hostedAccounts.map((account) => account.getAccountData()),
            actualRuns: this.runCounter, // Actual number of simulation runs executed by this server
        };
        this.worldDBManager.analyticsAddServer(currServer);
    }
}
module.exports = AccountCluster;

# Model 3 Simulation

The Model 3 simulation extends the basic structure Model 2 was built on and adds key features that result in more realistic spending patterns.

## Primary Changes

- Improve code readability for future developers
  - Update variable names
  - Implement classes that adhere to the Single Responsibility Principle
  - Convert JavaScript to TypeScript (Object Oriented programming allows for more extendibility)

- Collect data from simulation that can later be analyzed
  - Add analytics table to WorldDB that records both server and world information
  - Export to useable files

- Add extendable accounts classes to simulation
    - Future deveopers/interested parties can add different account types to represent real world entities
        - retailers
        - investors
        - consumers
        - manufacturers
        - etc
    - The amount of each account type present in the simulation can be changed in the configuration file

- Add extendable action classes to simulation (these are the actions that accounts will take while the simulation runs)
  - Future developers/interested parties can create actions that accounts will take during the simulation
    - find clients
    - sell merchandise
    - get paycheck
    - give loan
    - etc
  - Actions can be added to various accounts
  - The frequency of occurence for each action is determined by the account class they are assigned to

- Perform credit lifts during simulation run time when criteria are met

## Running the Simulation

To run the simulation you need to follow these steps:
1) Run `npm install` 
2) Export environment variables*
3) Follow steps 4-5 under Developement (below)
    
\*For an in-depth explanation, please see the [setup instructions](/doc/sim-docker.md).

### Analytics

One of the primary goals of the simulation is to gather analytical data to prove the viability of MyCHIPs in the real world. The simulation exports data to MongoDB throughout execution, but the data must be exported after the simulation is complete. We have created a script that exports the MongoDB data to a local folder in JSON files. 

Run `npm run getAnalytics` after the simulation ends but before running `./simdock shutdown` to export simulation analytics to the `test/sim/local/analytics` directory. (See step 4 under Developement below)
## Development

<ins>_ Do not edit Model 3 JavaScript files directly _</ins>

The simulation Model 3 was developed using TypeScript to allow clear data typing, extendable classes, and inheritance. Changes must be made to the `*.ts` files. Any changed `*.ts` files must be transpiled before execution. 

The easiest way to run steps 2-3 is by running the npm script `npm run runsim` (\*see note below). The overall work flow should look something like this:

1. Edit `*.ts` files.
2. Run `npm tsc` before running the simulation.
3. Run `./simdock startup`, `./simdock tickets`, and then `./simdock start sim --runs=50` as outlined [here](/doc/sim-docker.md).
4. (Optional) Run `npm run getAnalytics` after the simulation ends but before running `./simdock shutdown` to export simulation analytics to the `test/sim/local/analytics` directory.
5. Run `./simdock shutdown` to end the simulation (this stops all simulation docker containers)


\*Instead of running steps 2-3 individually, developers may find it useful to run the `runsim.sh` bash script within the `lib/agent3` directory, which executes these steps in sequence. This can be done with the command `npm run runsim`. Since the simulation is run asynchronously, the script should be run from the command line. We've seen some issues with using VS Code's NPM SCRIPTS runner.
## Creating Accounts/Actions

To add new accounts, implement "account.ts" and place the new account class file in the "/accounts" directory. Typescript will enforce implementation of class methods.

``` 
import Account from '../account'

class NewAccountType implements Account { ...
```
The process to add new actions follows the same pattern: implement "actions.ts" and place the new account class file in the "/actions" directory. Typescript will enforce implementation of class methods.

```
import Actions from '../actions'

class NewAction implements Action { ...
```
TODO: add some text here to describe how to add actions to accounts...

## Prettier & ESLint

This project uses esLint and Prettier to format and check the simulation TypeScript files for syntax errors. Make sure to set up your IDE to use these tools (preferably Prettier formats on each save). To format everything at once, run `npx prettier --write .` . Before committing, make sure to run `npm tsc` to apply style changes to JS files as well.

## Structure Overview

The MyCHIPs project and Model 3 code have a lot of moving pieces that come together to make the simulation work. Along with Kyle's well-written and thorough documentation, we wanted to provide a sort of summary of the pieces at play that are crucial for the simulation Model 3.

Details on low-level implementation are provided in the code as Javadoc comments, and this README contains high-level explanations that will help you see how the different pieces fit together. We encourage you to add clear documentation as you develop to mantain continuity during the development process.

Here is a basic description of the flow of data through the simulation:

1. `simdock.sh` takes care of setting up the environment required by the simulation.

   - Starts the local SQL databases (one container per site) and world database (MongoDB)
   - Creates and inserts users into the local SQL databases
   - Runs `sim-c.sh` which starts the simulation by creating one 'model' docker container per site, each running an AccountCluster process (the entrypoint is `test/sim/account` which instantiates the main class in `model3.ts`)

2. Each 'account' (by running AccountCluster) loads the config file parameters, connects to their respective local SQL databases, and connects to the shared Mongo 'World' database.
3. Accounts stored in local SQL databases are loaded into their respective sites' AccountCache, and are loaded into the shared WorldDB.
4. 'accounts' iterate through their local accounts, performing allowed actions, (such as purchase item, take out a loan, sell a good, etc...). For example, let's say Dave initiates a 'purchase item' action. To do so, he needs to find a new spending target. His account goes through these steps:

   1. Find peer in world DB (Mongo)

   2. Do we have the peer's info already downloaded?
      1. If yes, look up the peer's ID in our cache
      2. If not, add peer to our MyCHIPs DB (PG)
         This gives the peer a new ID on our server (different than their ID on their server)
         . If they are on a different server, ask them to download our info to their server
   3. Once our info is on the peer's server...
   4. Use the peer's ID (not peer_cid) to make a connection (tally) request with SQLManager

5. Once the peers and SQLManager approve the connection, then the peers perform the tally behind the scenes of the simulation.

6. Listeners to the SQL databases' peers or tallies will notify the 'agent' container of new change, and the 'agent' reacts accordingly

### Simulation Sequence UML

![Sequence UML](../doc/sequence-UML.png)

### Model 3 Class UML Diagram

![Agent 3 Class UML](../doc/class-UML.png)

## Debugging Tools

- To query SQL databases, use `./simdock q <int-for-server-num> "<sql-query>"`
  - \*Example: `./test/sim/simdock q 0 "select id, peer_cid from mychips.peers_v"`
- SQL DB field name mappings can be found in the `baseAccounts.ts` getAccount() method
- Relevant PostGres Schemas
  - Users
  - Tally
  - Chit (like a check) (payment of X chips)

## Gotchas

- Before running the simulation for the first time, make sure you ran `npm install` and exported the correct environment variables as indicated in the [setup instructions](/doc/sim-docker.md)
- The Actions collection in the World DB is a shared queue where servers can tell eachother perform actions. No relation to our actions class.
- Currently a user's id is unique only on their host server, while the peer_cid is unique to the world. This means two users with different peer_cids could have the same id on a server when one is downloaded as a peer. Kyle is working to make peer_cids the only identification needed and remove the need to download a user as a peer.
- If you modify the config before you run killsim, the command will not work correctly. Make sure you only make changes to config.dock after you kill a simulation. (For example, if you change from 10 sites to 4, then run killsim it will only destroy containers and data for the first 4 servers, but will leave all of the others)

## Glossary

CHIP - A unit of digital credit in the MyCHIPs system

Chit - A payment of X amount of CHIPs. Can be thought of similar to writing a check.

Chad - A chad is the current way of identifying an account. When an account is trying to create a tally, it finds a random chad and makes a tally request to the account associated with that chad.

Tallies

- Tally is a contract between two accounts that consists of a stock and foil
  - \*Multiple transactions can happen on a single tally 
  - As you make multiple transactions it results in an increase to the stock/foil amount, rather than an increase in the amount of tallies.
  
Stock - an income source / positive change to your balance
- someone (client) is paying you (vendor)

Foil - a spending target / negative change to your balance

- person (vendor) you (client) are paying

Process of making a payment

- Account (you) finds a vendor (walmart) to give money to. (This represents a loan, gift, payment, etc.)
- Asynchronously check for peer inside worldDB (right now it's random)
  - Find someone that isn't ourselves that we aren't connected to
- If failed, try again
- If success, check if person exists in our cache, add then add them if not. (TODO: See if we need a way to update this info or not)
- Add them to our peer server which gives us
- ID's are different on different servers

## Future Development (TODO's):

- Change SQL schema to allow ent_type to have more that one VARCHAR
- Move usergeneration from ./simdock start sim to Agent Cluster setup code so the simulation model can manage account creation.
- Use async/await and promises instead of callback hell
- Create a version of simdock for large scale simulations that does not open terminals or browser windows
- Get performance data for large scale simulations and discover limitations on memory and disk space.
- Figure out why the touch command can't create files and make sure they are deleted in killsim
- Simulation memory can work sporadically with asynchronous calls in large simulations. We need to look into synchronous container creation.
- Add criteria for credit lifts to the config file to test various lift scenarios

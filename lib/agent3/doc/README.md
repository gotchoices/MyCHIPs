# Agent 3 Simulation

The Agent 3 simulation extends the basic structure Agent 2 was built on and adds key features that result in more realistic spending patterns.

### Primary Goals

- Improve code readability for future developers (Completed)
  - Update variable names
  - Implement classes that adhere to the Single Responsibility Principle
  - Convert JavaScript to TypeScript
- Collect data from simulation that can later be analyzed
  - Add analytics table to WorldDB that records both server and world information
  - Export to single file
- Add configurable actions to simulation
  - Easily allow other developers to create their own actions
  - Actions (such as purchase a house, buy a car, or get a paycheck) can be configured with their frequency depending on the account type
- Perform credit lifts when criteria is met

## Structure Overview

\*Details on low-level implementation are provided in code as Javadoc comments

Here is a basic description of the flow of data through the simulation:

1.

### Agent 3 Class UML Diagram

![Agent 3 Class UML](../doc/class-UML.png)

### Simulation Sequence UML

![Sequence UML](../doc/sequence-UML.png)


Notes 
Simdock (We haven't changed anything)
- startup starts the databases
- start_agent - starts up docker container,
  - usercheck checks to see if it has enough local users (by checking the user_ent field that is unique to local accounts) and then generates accounts using randUser to populate postgres database with accounts,
  - One of each container per site
- runs sim-c which starts AgentCluster
- To query, use './simdock q <int-for-server-num> <sql-query>
  - Example ./test/sim/simdock q 0 "select id, peer_cid from mychips.peers_v"

baseAccounts.ts getAccount() is a good key 

- Action collection (world DB) is a shared queue where servers can tell eachother to do stuff. No relation to our actions class

- Relevant PostGres Schemas
  - Users
  - Tally
  - Chit (like a check) (payment of X chips)

- Listeners: 
  - any parameter updates (not currently used)
  - peers or tallies to notify of new change (to do the change)

- Performing a tally
  - Connections between peer servers are managed with SQLManager. Once the peers and SQLManager approve the connection, then the peers perform the tally behind the scenes.

Proof of Contract
- Tally is a contract between two accounts that consists of a stock and foil
  - \*Multiple transactions result in an increase in stock/foil amount, rather than an increase in the amount of tallies.
  - Stock -> income source -> someones (client) paying you (vendor)
  - Foil -> spending target -> person (vendor) you (client) are paying

  	p0
		peer_cid: server id
		   a:      p1000
		   b:      p1001
		   c:      p1002
		   e: p1003

	p1
		d: p1000
		e: p1001
		f: p1002

    find new spending target

  // 1. Find peer in world DB (mongo)
	// 2. Do we have the peer's info already downloaded?
	//	a. If yes, look up the peer's ID in our cache
	//	b. If not, add peer to our MyCHIPs DB (PG)
	//		This gives the peer a new ID on our server (different than their ID on their server)
	// 3. If they are on a different server, ask them to download our info to their server
	// 4. When our info is on the peer's server...
	// 4. Use the peer's ID (not peer_cid) to make a connection (tally) request

Process of making a payment
- Account (you) finds a vendor (walmart) to sell you something
- Asynchronously heck for peer inside worldDB (right now it's random)
  - Find someone that isn't ourselves that we aren't connected to
- If failed, try again
- If success, check if person exists in our cache, add then add them if not. (TODO: See if we need a way to update this info or not)
- Add them to our peer server which gives us 
- ID's are different on different servers

TODO: 
- Change SQL schema to allow ent_type to have more that one VARCHAR
- Quick explanation of how typescript works and run tsc
- Move usergeneration from ./simdock start sim to Agent Cluster setup code
- Add environment variables to runsim.sh
- Use async/await and promises instead of callback hell
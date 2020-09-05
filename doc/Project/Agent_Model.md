# Agent Model Enhancements
July 2020

## Project Background:
A MyCHIPs network operates on the premise that in a sufficiently developed
network of private credit contracts, it will be possible to clear most credit
imbalances by:
- discovering circular, upstream pathways through the network; and
- executing an atomic transaction around the circuit to reverse some or all of the imbalance.

As of the initial proof-of-concept release, there are a number of unknowns, including:
- will the imbalances in a real network converge to desired balances?
- how many nodes are required to get the critical mass required for a functioning system?
- how many upstream (stock) and downstream (foil) credit agreements are optimal for each node?
- how will real entities (people and companies) adapt to imbalances that fail to clear?
- how many degrees of separation are likely to be necessary to reach an abitrary node
  in a population of a given size (when performing linear lifts).

The MyCHIPs source distribution includes a simulation environment which can launch a
predetermined number of instances of the server, each running in a Docker container.
It also includes a rudimentary simulator which attempts to act as individual agents
(people and companies) would in a real life network.  However the simulator follows
a very simple model--much too simple to accurately model the choices real entities
would make in actual use.

## Objectives:
The goal of this project is to enhance the agent code to more accurately model the
kinds of choices real people and companies make when faced with economic challenges,
and then to run the model at varying scales in order to evaluate and predict the 
efficiency of a private credit network in actual operation.

Examples Include:
- The more you have, the more you spend
- The less you have, the less you spend
- If you have too little, you will try to earn more or find better income streams
- How much savings are you comfortable with?
- Seek/establish vendors, in addition to clients
- Honor settable max clients, max vendors parameters from DB
- Raise vendor accumulation limits if my receivables get high
- Create lift incentives if I accumulate stale imbalances
- Extend credit to peers based only on their credit-worthiness
-   Be more random on search for new client tally connection
-   Find a foil tally and pay some credits on it
-   Agent establishes reasonable number of tallies with other users
-   If I already have a tally with you, don't do another one
- Set real values for all trading parameters
- Establish some long-term collateralized savings tallies (mortgages)

## Outcomes:
- Understand existing simulation code
- Design more robust architecture for code
- Implement new code design
- Run the model at scale
- Collect and analyze the distributed data to answer questions above
- Publish research results

## Technical Considerations:
The production MyCHIPs server uses an SQL database for storing its model data.

The current simulator uses a Javascript/NodeJS process to to iterate through
the local users on a system, acting in sequence on behalf of each local user.

The current simulator also includes a MongoDB instance, part of the simulation 
environment only (not a production component) that models the "real world" where 
entities meet and establish tallies with each other "out of band" from the 
actual MyCHIPs network.

The Docker environment will likely need to be enhanced to allow launching of
containers in the cloud to achieve the full-scale simulations necessary for
complete testing.

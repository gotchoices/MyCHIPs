# Agent Model Enhancements
Sep 2021

## Project Background:
A MyCHIPs network operates on the premise that in a sufficiently developed
[network](/doc/Protocol.md#network-assumptions) of [private credit contracts](/doc/Tallies.md), it will be possible to 
[clear most credit imbalances](/doc/Protocol.md#credit-lifts-explained) by:
- discovering circular, upstream pathways through the network; and
- executing an [atomic transaction](/doc/Lifts.md) around the circuit to reverse some or all of the imbalance.

In a MyCHIPs network, a credit imbalance is simply defined as: 
Any balance of [CHIPs](http://gotchoices.org/mychips/definition.html) on a tally in excess of
what what the user has established as the [target level](/doc/Tallies.md#trading-variables) of CHIPs.

Imagine you hold an upstream tally stock with your employer and you hold a downstream tally foil with a
market where you like to buy your groceries.  When you employer pays you with his credits, you will
hope he has a strong enough set of connections further upstream to provide lift pathways whereby you can
convert his credits into the grocery credits (on your downstream tally foil) you actually need.

It is theorized that human beings, making rational economic decisions in their own interest, will
gradually adapt, organizing themselves into a network that is capable of effectively clearing most, if
not all, credit imbalances.

As of this writing, that has not been proven and there are still a number of unknowns, including:
- will the actual CHIP balances in a real network converge to target balances?
- how many nodes (people or companies) are required in order for a network to be able to effectively clear credit imbalances?
- how many upstream (stock) and downstream (foil) tallies on each node are optimal for effective credit clearing?
- how will real entities (people and companies) adapt to imbalances that fail to clear?
- how many degrees of separation are likely to be necessary to reach an abitrary node
  in a population of a given size when performing [linear lifts](/doc/Protocol.md#credit-lifts-explained).

The MyCHIPs source distribution includes a [simulation environment](/test/sim/README.dock) which can launch a
predetermined number of instances of the server, each running in a Docker container.
It also includes a [rudimentary simulator](/lib/agent2.js) which attempts to act as individual
people or companies might act in a real life network.  However the simulator (version 2) follows
a very simple model--much too simple to accurately model the choices real entities
would make in real life.

## Objectives:
The goal of this project is to create a more sophisticated agent model (version 3) which will more accurately model the
kinds of choices real people and companies make when faced with economic stimuli,
and then to run the model at varying scales in order to evaluate and predict the 
efficiency of a MyCHIPs network to discover and clear credit imbalances in actual operation.

Here are some examples of economic decisions people and companies might make, that are not accounted for in the version 2 agent model:
- The more you have, the more you spend
- The less you have, the less you spend
- If you have too little, you will try to earn more or find better income streams
- How much savings are you comfortable with?
- Seek/establish vendors (downstream), in addition to clients (upstream)
- Honor the settable maximum clients and  maximum vendors parameters in the database
- Raise vendor lift targets (desired CHIP levels) if my upstream receivables get toohigh
- Create lift incentives (willing to pay a lift fee) if I accumulate stale upstream imbalances
- Extend credit to peers based only on their credit-worthiness
-   Be more random on search for new client tally connection
-   Find a foil tally and pay some credits on it
-   Agent establishes reasonable number of tallies with other users
-   If I already have a tally with you, don't do another one
- Set real and reasonable values for all [trading parameters](/doc/Lifts.md#trading-variables)
- Establish some long-term collateralized tallies (mortgages) as a savings mechanism

## Milestones:
- Understand existing simulation code
- Extend simulation code to allow high number of server instances running in the cloud
- Design new, fully configurable agent 3 code model
- Implement agent 3 code
- Run the agent model at scale
- Collect and analyze the distributed data set to answer as many unknowns as possible
- Publish research results

## User Interface:
Each instance of an agent should contain a variable modeling the simulated user's tendency for a certain economic behavior such as those noted above.
For example, some people tend to save a lot of money.  Others may spend money just as fast as (or faster than) they earn it.
Users of the simulation should be able to tailor simulation runs to modify the behavior of the population of agents.

It is more important to focus on the substance of the simulation than it is to take time coding a fancy user interface.
For example, it is suggested to configure the simulation using simple text (YAML) files.

As agents are instantiated, they should randomly select values for each of the programmed behavioral variables.
However, the configuration should allow the operator to control:
- A minimum for each variable
- A maximum for each variable
- A distribution of agents (what percentage of the population falls in a specified range of values for a given variable)

## Technical Considerations:
The production MyCHIPs server uses an SQL database for storing its model data.
As the simulator runs, it will create its own set of randomized data across the
community of running agents and their host servers.  This data may be analyzed simply
by issuing SQL commands to the various servers.  The existing simulation environment
supports issuing arbitrary SQL commands to one or all database instances.

The current simulator uses a Javascript/NodeJS process to to iterate through
the local users on a system, acting in sequence on behalf of each local user.
The version 3 agent model might benefit from a more efficient model such as a
separate, asynchronous instance for each agent.

The current simulator also includes a MongoDB instance, part of the simulation 
environment only (not a production component) that models the "real world" where 
entities meet and establish tallies with each other "out of band" from the 
actual MyCHIPs network.

There exists a secure, encrypted API for users to communicate with MyCHIPs
server instances.  However the agent models typically bypass this layer and write
records direct to the SQL database for the sake of efficiency.  The version 2
agent model can serve as an example of how to communicate with both the production
SQL database as well as the Mongo instance.

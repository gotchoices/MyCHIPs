## Objectives for User Agent Model:
Jan 2019 (Some information may be outdated)

This is not a part of the production MyCHIPs server, but rather a tool to aid
in the development of the network algorithms.  The idea is to spawn a number of
servers and databases, each of which contain a number of users.  The agent
model acts on behalf of each of the created users, initiating tallies and 
making trades.  This should create a database of transactional data rich enough
to demonstrate the challenges of executing a credit lift.

An external script will be used to create a specified number of users in a
target database.

Then, the MyCHIPs server will be launched with the agent model enabled.  This
will run a cycle on specified intervals to allow each users's agent to execute
transactions.

The model should be able to receive asynchronous notifications just as a real 
user would and act on those events.  The decisions can be randomized, within
reasonable constraints.

Agent Decisions:

Tallies:
  - Decide to open new stock relationships (employers, clients)
    This represents a job or income stream, so each should get at least one
    We can query to find entities that don't have too many vendors and try them
  - Respond to new foil invitations (suppliers, employees)
    Establish a random max limit for this (how big a consumer am I?)
  - Request to close an occasional stock tally (quit job)
  - Request to close an occasional foil tally (fire employee or supplier)
  - Randomize cr_limit, dr_limit on tallies
    
Chits:
  - Randomize a fixed amount to request on each stock tally each cycle
  - Enter requests for these payments
  - Respond to pay requests, randomize answers, but usually yes
  - Respect cr_limit, dr_limit

Lifts:
  - List stock chits available to trade
  - Request foil chits needed in trade
  - Output queries necessary to populate database of links/pathways
  - Respond to such queries

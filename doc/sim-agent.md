## Agent Model
Most of this file was created before the agent model was coded and so primarily
expresses design objectives.

In conjunction with the various iterations of the simulation environments, several
versions of the agent model have been coded, or are in process.  These versions
are located in the lib directory and invoked from the test/sim/agent script.

Versions 1 and 2 are very rudimentary and were coded and used to validate the 
early lift algorithm.

Version 3 is the subject of a BYU Capstone project (2021/2022) and will hopefully
incorporate many more of the features outlined below.  The specific project 
objectives are outlined [here](Project/Agent_Model.md).


## Objectives for User Agent Model
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

<br>[Next - Learning About the Software](learn.md)
<br>[Back to Index](README.md#contents)

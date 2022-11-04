## Agent-Based Modeling

In conjunction with the various iterations of the simulation environments, several
versions of an agent modeler have been coded, or are in process.  These versions
are located in the lib directory and invoked from the test/sim/modeler script.

## Modeler Version 1
This modeler is very simple, but still useful.  It only contemplates users on a
single site so is not of much help in evaluating distributed lifts.  However it
will generate interesting data sets on a single site so you can visualize and
test local lifts, both circular and linear.

To use it:
- Start with a clean (or non-existent) database
- Launch a server instance: npm run server
- Connect the [admin browser UI](use-admin.md)
- Initialize the database: cd test/sample; ./kickstart
- Create some sample users: ./randuser -n 10
- Launch the modeler: test/sim/model -m 1

More detailed explanation [here](use-test.md).

## Modeler Version 2
Version 2 is built to handle multiple sites and simulate distributed lifts.
This is the default the [docker-based simulation](sim-docker.md#containerized-simulation)
was built for.

## Modeler Version 3
Version 3 is the subject of a BYU Capstone project (2021/2022) and will hopefully
incorporate many more of the features outlined below.  The specific project 
objectives are outlined [here](Project/Agent_Model.md).


## Objectives for User Agent Model
Jan 2019

Much of the following was created before the agent model was coded and so primarily
expresses design objectives.

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

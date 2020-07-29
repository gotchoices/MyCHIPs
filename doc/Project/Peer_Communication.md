# MyCHIPs Peer-to-Peer Communication Module
July 2020

## Project Background:
The MyCHIPs protocol supports a fully distributed system of private credit
relationships which can be used to exchange, clear and transmit value.
Simply put, it implements a monetary system.

Individual user accounts are hosted on a set of servers (or systems of servers)
which are shown on this [LibreOffice figure](/doc/Scaling.odg).  The system
model data are contained in the PostgreSQL database.  There is one such
database per "node" in the network.  But there may be multiple NodeJS servers
which direct traffic to/from the model and also provide a certain amount of
control logic.

Specifically, there are shown one or more "Peer Servers" which are merely
processes that communicate with other similar nodes on the MyCHIPs network.
The low-level communication portion of this process is currently implemented 
in [this file.](/lib/peercomm.js).

The strategy is to always present a pathway for messages to any other node on
the network with which we may share a tally (credit relationship).  Although
such connections may not always be open from a sock standpoint, they need to
appear virtually open to the state machine logic.

The current implementation will check to see if a socket connection is already
open to the intended destination.  If so, packets will simply be sent over
the existing connection.  If the connection is not open, the code will attempt
to open a connection.

The reality of Unix sockets is based on a server/client model.  So in open 
connections between two nodes, one node will be the server and the other will
be the client.  But MyCHIPs is a peer-to-peer system so there is no meaning
to who is the server and who is the client.  All nodes listen as servers at
all times and so who is client really depends on which node initiated the 
current connection.  And that can change if a connection times out, closes,
and then is reopened by the opposite peer.

## Objectives:
The goal of this project is to bring encryption and connection security to the
peercomm.js module.  All communications need to be completely private to the
two participating nodes.  And nodes need to be assured that they are
communicating with the indended trading partner's node.

## Strategy:
The current intention is to use an existing framework called
[Noise Protocol](http://www.noiseprotocol.org/) which allows one to establish
an encrypted communication channel using a fairly simple set of parameters.

If a different method is used, it should be equal or superior to the 
functionality that can be provided from Noise Protocol.

## Outcomes:
- Existing MyCHIPs code base can be operated over new code base with fully
  encrypted and authenticated endpoints.
- Code accesses existing public key data from PostgreSQL database to authenticate
  opposite endpoint.
- System uses additional ephemeral keys so that session data is safe from
  replay attacks.
- MyCHIPs can be run with new code base or without (for increased speed when
  running simulations).

## Technical Considerations:

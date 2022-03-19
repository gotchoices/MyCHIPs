# Referee Server
Mar 2022

## Project Background:
The initial 0.x protocol suffered from several fatal flaws.
Notably, it could not be guaranteed that a lift would ever terminate.
There was an inherent tradeoff between safety and [liveness](https://en.wikipedia.org/wiki/Liveness).

These problems have been addressed by the [enhanced 1.x protocol](../learn-protocol).
This protocol has not yet been [fully implemented](State_Machine.md) but that effort is in progress.

An important part of the fix is the addition of [referee nodes](../learn-protocol.md#referee-queries)
in the system.  These nodes are proposed as arbiters at the beginning of each lift cycle and must
be agreed to by each node participating in the lift.

The sole job of the referee is to decide when a lift has gone long enough to expire.
The referee is expected to answer correctly and consistently about any given lift:
- that it has not yet expired and has an unknown outcome; or
- that it has been duly signed by the originator (and the referee itself); or
- that it has expired without ratification and can safely be ignored.

Referees are expected to save ratification signatures for a *very long time* if not indefinitely.
They are expected to be reliable in terms of:
- Response time
- Network connectivity
- System up-time
- Consistency
- Integrity

## Objectives:
The MyCHIPs server process is really multiple servers in one.
The process can currently be launched with services for any of the following:
- Server for SPA user and admin web applications
- Contract document server
- Peer-to-peer traffic server (agent)
- Lift/route checker/scheduler

In small systems, a single process can serve all functions.
In larger systems, separate processes can be launched that specialize in just one or two.

The goal of this project is to implement a working referee server object according to the published protocol specification.

## Strategy:
- Determine the appropriate network protocols to service.
- Implement servers to answer each of those protocols.
- Design a database schema to store lift objects and their signatures
- Implement a process that can answer inquiries and store signatures on the fly

## Outcomes:
- Referee code is stable and ready for production use
- Full regression tests exist for the implementation
- Multiple server processes surrounding a single database can operate consistently in concert
- Multiple server processes may include servers communicating over a variety of network protocols

## Technical Considerations:
- One supported protocol should be https.  This will be used where the referee is identified
  by a domain that can be verified through regular Certificate Authorities.
- Another supported protocol should http.  This will be used where nodes already know the
  public key (by other means) of the host (or IP number) being suggested as referee.
- Another supported protocol should be noise protocol, according to the regular implementation
  being used for peer-to-peer message exchange protocol.  In other words, any MyCHIPs agent
  address can be a suitable referee address.  Nodes are responsible to know the public key
  (by separate means) for such referees.

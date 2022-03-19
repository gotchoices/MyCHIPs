# Peer-to-Peer Protocol Hardening
Mar 2022

## Project Background:
Since the [enhanced 1.x protocol](../learn-protocol) was released, there has been
a great effort put into improving the code that handles communication between 
sites and agents.  This included:
- Implementing noise protocol encryption between nodes
- Developing the [CHIP address](learn-users.md#chip-addresses) standard
- Refactoring the state-handling code for peer-to-peer messages
- [Documenting](learn-messages.md) the message format

What has not yet been skipped over in this effort is creating a way to be resilient
to temporary network disruptions.  At the moment, if a message is lost, the
natural progression of a tally, chit, route or lift will likely stall out.

The schema for each subsystem includes a table for storing retries.  These tables
are partially seemed into the code, but there are no actual handlers to deal with
packets that are lost or corrupted.

## Objectives:
The goal of this project is to improve the protocol to ensure reasonable safety
completion of all intended transactions even if network connectivity is disrupted
for any period of time.
- Implement a packet retry method, hopefully using the existing retry schema
- If this is not feasible, re-design the retry schema
- Implement full unit tests to simulate disconnections/reconnections
- Implement integration tests to show the system works correctly across multiple nodes.

## Strategy:
The current state diagrams detail states that:
- Require user attention; or
- Require agent attention.

When a state transition occurs into one of these states, a notification is sent to any
process that may be listening for it.  If the process is unavailable at that moment, 
the message may be lost.  The schema also includes stored procedures that will
re-generate any message that may be necessary.  So when agent and user processes
start up, they should run these procedures to see if any traffic has been lost while
they were away.

In addition, messages may be lost in transit from one node to another.  When an agent
transmits a message with a timeout attached, it should set a local timer to be reminded
when it is time to recheck the activity (chit, tally, route, lift, etc.)  associated 
with that timer.  If a confirmation is handled by the same agent proving that the retry
is not necessary, the applicable timer can be canceled.

When the timer triggers, a query of the database can be made to see if a further retry
is still necessary.

## Outcomes:
- Agent processes can stop and be restarted without missing any critical message traffic
- User processes can disconnect/reconnect without missing any critical message status
- Network connection between sites/nodes/agents can be lost for a time and all subsystems will
restore their proper status upon reconnection.
- Full regression tests exist for the implementation

## Technical Considerations:
Official state of the system is defined by the SQL database.
Any message that is inconsistent with that state is expected to be ignored or otherwise
should not bring harm to the proper operating state of the system.

In other words, a lost message can reappear long after retries have solved the problem
and the reappearing message must not damage the intended system state.

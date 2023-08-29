# Tally Protocol Testing
Aug 2023

## Project Background:
The [MyCHIPs 1.x protocol](../learn-protocol.md) defines a series of messages that pass back 
and forth between two parties (Originator and Subject) as they establish a Tally relationship.

There are established [tests](../work-testing.md) for running the schema through its expected uses.
Specifically, the file "sch-tally.js" attempts to test each valid state transition.
The file "tally.js" launches instances of the peer-to-peer server and actually simulates a tally being established between two users.

As of this writing the tests do not extensively test edge cases or exceptions to the normal, expected behaviors.

## Objectives:
This project is meant to:
- Expose a developer to:
  - general project structure
  - testing environment
  - schema build environment
  - tally negotiation protocol
- Evaluate whether a developer has the talents/skills to help move the MyCHIPs project forward.
- Improve the resilience of the tally negotiation protocol
- Hopefully, engage long-term to enhance the backend server in other areas as well

## Strategy:
- Clone the MyCHIPs repo
- Run test suite: npm test
- Run the tally chain: npx mocha impexp testusers user2 tally
- Download the MyCHIPs mobile app
- Sign up for test account on mychips.net
- Run the tally negotiation sequence with another user to see how tallies get started
- Hypothesize possible edge cases:
  - What types of things can go wrong during tally negotiation, for example:
  - Network connection disrupted
  - One user offline
  - User modifies tally in unexpected ways and counter-offers
  - One user's tally copy gets deleted or voided mid-process
- Write tests for such edge cases
- Find one or more that expose failures in the implementation and/or protocol
- Suggest improvements to the implementation and/or protocol
- Implement improvements to the implementation and/or protocol

## Outcomes:
- Backend support is improved for edge cases in tally negotiation
- Users can salvage partially negotiated tallies and complete process to open tally
- Users intentions to tally (or not tally) can be achieved in all cases
- The developer is familiar enough with the system architecture to move on to more complex test cases

## Technical Considerations:
- Testing probably easiest on Linux platform
- Might be possible on Mac (or possibly Windows) with proper docker support
- Will need a mobile device to test on a real-world server instance (mychips.net)
- May need two mobile devices (or a running simulator) to test real-world end-to-end
- Or can use a friend with another device to test real-world end-to-end

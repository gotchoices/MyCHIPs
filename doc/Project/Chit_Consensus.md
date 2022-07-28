# Chit Consensus
Mar 2022

## Project Background:
The initial 0.x protocol laid the groundwork for a system to assure that both ends 
(stock and foil) of a tally hold consistent versions of the chit history.
In order to do that, chits are added to a [hash-chain](https://en.wikipedia.org/wiki/Hash_chain)
so that separate nodes can quickly exchange on the ending hash to determine if the chains are
identical on each end.

Like a public blockchain, parties to a hash chain must follow a
[a protocol for reaching consensus](https://en.wikipedia.org/wiki/Consensus_(computer_science))
on the order of items added to the chain.

The [enhanced 1.x protocol](../learn-protocol) refined a [message exchange system and a protocol for this](../learn-protocol.md#chit-consensus).
This protocol has not yet been [implemented](State_Machine.md) but that effort is in progress.

## Objectives:
This project is to expand and enhance the current consensus code in MyCHIPs to fully implement
chit consensus as designed in the above protocol document.

## Strategy:
- Learn and understand the protocol document thoroughly
- Learn and understand the [current implementation](../../schema/chit.wms)
- Extend the implementation to handle edge cases where consensus is diffcult
  - Recovering from network disconnections or lost messages
  - Recovering from chits that are added at each side simultaneously

## Outcomes:
- Chits can be added at any time at either end of the tally
- Chits will always end up getting added to the official version of the chain in the same, consensed order
- Chits will never be lost
- Full regression tests exist for the implementation

## Technical Considerations:
- Chit consensus is handled in stored procedures inside the database
- This is important since the database is relied on to store the official, atomic state of the system
- The agent processes will need to be relied upon to pass chit consensus messages but not to make
  decisions or implement the consensus algorithm.

### Lifts: Behavioral Model


## Top Level Interface

# Nodes
  - Decide to accept or reject additional chits
  - Keep a record of all tallies
  - keep a record of all lifts
  - Reflect sum value of all valid chits in all the tallies
  - Reflect sum value of all conditional chits in all the tallies

# Tallies
  - Decide to accept or reject additional chits
  - reflect the total value of all valid (committed and acknowledged) chits (a number that is the sum of all values)
  - reflect the total value of all conditional chits
  - Have consensus with trading partner's tally (order and total)
  - Resolve consensus issues in a finite amount of time

# Lifts
  - Reflect the value of the conditional chits promised
  - Keep a record of data needed to Resolve the lift (Decide if the lift has completed, or has failed)
  - Identifies 2 or more chits whose sum is 0.

# Chits
  - Hold a record of the value transferred
  - Hold a record of acceptance by both parties
  - Hold a record of what contingencies must be met to make the chit valid


## Data


## Properties of Nodes
Nodes represent members of the trading community and capture the members credits, obligations, and tolerance for risk. Credits, Obligations and risk tolerance are tracked for individual trading partners and in aggregate. A node consists of:
  - A Set of Tallies
  - A Set of Lift Records
  - A Assets Balance that is a number equal to the sum of Stock Balances in it's set of tallies
  - A Debts Balance that is a number equal to the sum of Foil Balances in it's set of tallies
  - A Projected Assets Balance that is a number equal to the Assets Balance minus the sum of values of pending lift records
  - A Projected Debts Balance that is a number equal to the Foil Balance minus the sum of values of pending lift records
  - A Minimum Assets Balance. A number such that Minimum Assets Balance <= Assets Balance && Minimum Assets Balance <= Projected Assets Balance


## Properties of Tallies
  - Totals should only be provided after consensus
  - Decide to accept or reject additional chits
  - reflect the total value of all valid (committed and acknowledged) chits (a number that is the sum of all values) (This should only be provided after consensus)
  - reflect the total value of all conditional chits
  - reflect the total value of all (acknowledged but not committed) conditional chits
  - reflect the total value of all (committed but not acknowledged) unacknowledged chits
## Properties of Chits

## Properties of Cycles

Cycles are an ordered list of nodes such that:
  - Each node N has a tally with it's predecessor P and P holds the stock and N holds the foil.
  - Each node N has a tally with it's successor S and S holds the foil and N holds the stock.
    (Credits usually flow from successor to predecessor. During a lift they flow from predecessor to successor)
  - The Properties of Nodes above hold for every node

### Malicious behavior
 - You can't pretend to be someone else. (Appeal to Cryptography proof)
 - You can't falsify a signature. (Appeal to Cryptography proof)
 - Malicious actors cannot serve as arbiter. (An assumption)

### Things that may be problematic in the model:

  - A Node appears more then once in a cycle.
  - Interactions when a site authority signing lift chits for individuals 

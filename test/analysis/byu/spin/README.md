Spin Models to verify that 4 properties hold for the MyCHIPs credit lift algorithm

P1: Termination
  Lifts always eventually are committed or nullified for every active node. 
P2: Consensus
  At the final state of the lift, every active node agrees that the lift was committed, or every active node agrees the lift was nullified. 
P3: Harmless
  The balance of every active node on the final state of the lift is equal to or greater than its initial balance.
P4: Agreement
  Every active pair of nodes on the final state of the lift agree on their shared tally.

There are two models. One that is based on the protocol definition directly (the full model) and one that has simplifications that do not effect the final behavior but serve only as time optimizations (the minimal model).

These can each be verified to show that the 4 proeprtes hold using:
./verifyFullModel.sh
./verifyMinimalModel.sh


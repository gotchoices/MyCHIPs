# Lift/Tally Protocol Enhancements
July 2020

## Project Background:
A [professional analysis](/test/analysis/dsr/phase-1/results.md) was recently 
conducted to assess the viability of the lift protocol as documented and partially
implemented in the initial proof-of-concept release of the MyCHIPs reference server.
This analysis exposed several potential flaws which could cause the protocol to
fail, either leaving a group of participating nodes in an inconsistent state 
(safety), or failing to properly terminate a lift transaction (liveness).

There are several notable issues at the heart of the potential failures:
- We would like to think the lift proposer is honest and will only commit if it 
  can verify the affirmation of all participating nodes, within the proposed time 
  allowance for the lift.
- But since the network is fully distributed, it is difficult to know if the 
  proposer can be trusted in every case.
- It can also be difficult for a participating node to know for sure that the lift
  record has not been tampered with as it has been passed around the pathway for
  the proposed lift.
- Once the proposed time limit has been exceeded, it is difficult for participating
  nodes to know for sure whether to cancel the lift, or if they should wait a little
  longer to obtain a validating signature which might have been created in time but
  has not yet propagated to them.

## Objectives:
The goal of this project is to improve the protocol to ensure reasonable safety
and liveness without needlessly compromising project principles.  Among these
critical principles are the following:
- Points of centrality should be avoided wherever possible.  The system should:
  - retain virtually infinite scalability;
  - not present a single point of failure (attack vector);
  - not concentrate private data in central, public ledgers.
- Malicious attacks are to be expected and can not always be eliminated
- However damage from malicious attacks should be limited to the adjacent nodes
  the attacker is directly connected to.
- A malicious attack should be detectable and provable if possible by the
  victim (damaged party).
- A malicious attack should be a breach of a digital contract agreed to between
  the attacker and the victim.

## Strategy:
One suggested strategy is outlined in [this document](/doc/Safety).
It involves the introduction of an arbiter node who serves in a role similar to
a Transaction Manager (TM) in a traditional two-phase commit.  Specifically, the
proposer of the lift will choose a TM for the lift and furnish the TM with a
hash of the lift packet.  As the lift packet is propagated around the lift
pathway, participating nodes will be able to consult the TM to verify that the
lift packet still matches the hash held by the TM.

If/when the proposer decides to commit the lift, it will communicate this to the
TM, along with the validating signature for the lift.  If the TM deems this to 
have been done prior to the expiration time set forth in the lift packet, it will 
rule the lift as commitable and will be willing to share the validating signature
with any particpating node who is able to ask for it intelligently.  Generally
this will not be needed as the signature can circulate around the lift circuit
normally.  But in edge cases where a node goes down, or if the particpants become
partitioned, they will have the second option to reach out to the TM to complete
the lift (or to determine that it has been canceled).

In addition to lift protocol, there are also state machines to manage tallies,
chits, and routes.  These are much less of a concern from a safety/liveness
point of view.  However, they should also be reviewed, modeled and proven.

## Outcomes:
- Review/critique existing TLA+ code used in the DSR analysis
- Re-run the model checker to reproduce/validate the DSR results
- Modify the model to include the TM strategy outlined above.  This can be done
  in TLA+ or some other comparable model checker or algorithm proof tool.
- Evaluate the revised model for safety/liveness
- Modify the model according to any other strategies you may come up with.
- Evaluate your competing models for safety/liveness
- Compare all proposed protocol models, suggesting the one which provides
  the best overall performance according to project values and objectives.
- Publish research results

## Technical Considerations:
Typical consensus algorithms are based on the premise of a single transaction log
which is stored on multiple machines across a network--primarily for the purpose
of redundancy.  The network model typically assumes every machine can communicate
with every other machine.

In a MyCHIPs distributed lift, the network topology is a circuit.  Nodes can
communicate directly with their adjacent neighbor but not necessarily with other
nodes involved in the lift.  In fact most nodes won't know much at all about other
participants in the lift.  This interjects some differences and potential 
complications.

The current implementation only considers a case where a lift occurs as single 
thread rippling through a series of interconnected peers.  The possibility also
exists that a lift could split into two or more threads and rejoin later on.
This would allow multiple low-capacity pathways to combine to match a larger
capacity pathway somewhere else in the lift circuit.

It would also be helpful to eventually model the case where each node along
the way can retry multiple potential pathways until one is found that will
complete the circuit at the desired lift value.  Right now the implementation
will simply pick what it thinks is the best potential pathway and then succeed
or fail on that path.

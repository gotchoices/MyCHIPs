# Analysis Results

- [Prerequisites](#prerequisites)
- [Summary](#summary)
    - [Key Results](#key-results)
    - [General Recommendations](#general-recommendations)
- [TLA+ Specification](#tla-specification)
- [Issues In The Currently Implemented Protocol](#issues-in-the-currently-implemented-protocol)
    - [Issue 1: Invoice pend chits](#issue-1-invoice-pend-chits)
    - [Issue 2: Interlocking lifts](#issue-2-interlocking-lifts)
    - [Issue 3: Overlift in case non-originator node cancels timed out lift on its own](#issue-3-overlift-in-case-non-originator-node-cancels-timed-out-lift-on-its-own)
- [Protocol Options To Fix The Overlift Issue 3](#protocol-options-to-fix-the-overlift-issue-3)
    - [Option 1](#option-1)
    - [Option 2](#option-2)
    - [Comparison of Option 1 and Option 2](#comparison-of-option-1-and-option-2-behaviors)
- [Making Assumptions Weaker](#making-assumptions-weaker)
- [Issues When Assumptions Are Violated](#issues-when-assumptions-are-violated)
    - [Issue 4: Liveness issue due to crashed nodes](#issue-4-liveness-issue-due-to-crashed-nodes)
    - [Issue 5: Liveness issue due to malicious Lift originator](#issue-5-liveness-issue-due-to-malicious-lift-originator)    
    - [Issue 6: Safety issue due to collision of two malicious nodes](#issue-6-safety-issue-due-to-collision-of-two-malicious-nodes) 
- [Issues In The Current Source Code](#issues-in-the-current-source-code)
- [Recommendations For The Current Protocol](#recommendations-for-the-current-protocol)
- [Ideas For Further Research](#ideas-for-further-research)


## Prerequisites
1. It's assumed that the reader of this report understands how the Lift protocol 
is currently working by reading
    - [Got Choices](http://www.gotchoices.org/mychips/acdc.html)
    - Lift and Chit Sequence diagrams from `diagrams` folder
        - `lift_success.png` - General Lift flow in a positive case
            - Implemented in both code and TLA+ specification
        - `lift_cancel_option1.png` - [Option 1](#option-1) for the Lift protocol in the negative cases
         (when it can not be committed successfully) where timeout is coordinated by the Lift originator. 
            - Case 1 is implemented in the both source code and TLA+ specification
            - Cases 2 and 3 are implemented in the TLA+ specification only  
            - Case 4 is implemented in neither source code nor TLA+ specification            
        - `lift_cancel_option2.png` - [Option 2](#option-2) for the Lift protocol in the negative cases
         (when it can not be committed successfully) where fail and timeout messages can go in downstream direction only
         (the same as commit messages in the positive case).
            - Case 1 is implemented in the both source code and TLA+ specification
            - Case 2 is implemented in TLA+ specification only
            - Case 3 and 4 are implemented in neither source code nor TLA+ specification
        - `chit.png` - Chit payments workflow
            - Implemented in the both source code and TLA+ specification
    - `doc` folder from the source code
        - `Lifts`
        - `Tallies`
        - `Lifts.odg`
        - `States.odg`
2. It's also assumed that the reader understand what is 
    - [Safety property](https://en.wikipedia.org/wiki/Safety_property) of a  distributed system
    - [Liveness property](https://en.wikipedia.org/wiki/Liveness) of a  distributed system 
    - [Partial (or weak) synchrony](https://decentralizedthoughts.github.io/2019-06-01-2019-5-31-models/) communication model
3. Please note, that when we talk about malicious actions, we assume that economical and
[game theory](https://en.wikipedia.org/wiki/Game_theory) principles are applied,
and a node never does anything which can make it a looser. So, by malicious actions we mean an action
that can either have a benefit for the node, or can harm other nodes much more than it harms
(if harms at all) the malicious node.  
4. Usually in the provided examples  
    - We consider a Circular lift with `A`->`B`->`C`->`D`->`A` (downstream) payment flow,
    so that for the tally between `A` and `B` we have `A` as a Foil and `B` as a Stock. 
    - We assume that all nodes belong to separate hosting sites.
    - We assume that Phase 1 - Route Discovery has already been done and so we analyze
      Phase 2 - Conditional Commitment (or Proposal) and Phase 3 - Final Commitment (or simply Commitment) only.
    - Usually we assume that `A` initiates a lift (becomes a Lift's originator) and `B` is a Lift destination.
    - We call all nodes except `A` (Lift originator) as non-originator nodes.
    - Projected balance of a node for the given tally is calculated by taking into account both `good` and `pend` chits
    (that is a pending but not committed lift affects projected balances only). 
    - Available balance of a node for the given tally is calculated by taking into account `good` chits only     
    (that is a committed lift affects both projected balances and available balances).
    - We use `-` sign for Foil balances and `+` sign for Stock balances.
    - We assume (for simplicity) that nodes should not do lifts above zero from the Foil's point of view.
      Otherwise an overlift will happen.
      We consider the overlift as one of the main violations of the safety property,
      as in practice it may mean for the Foil that he or she gets more coupons from the Stock than wanted,
      so this coupons will be just useless or a waste of money/chips. (Please
      note, that in practice a non-zero debit limit can be used.)

## Summary

### Key Results

- Our tests and analysis found a number of issues that can and must be fixed 
(see [Issues In The Currently Implemented Protocol](#issues-in-the-currently-implemented-protocol) and
 [Issues In the Current Source Code](#issues-in-the-current-source-code)).
In particular, either [Option 1](#option-1) (modeled and tested via TLA+ model), or [Option 2](#option-2) (not tested yet)
can be implemented to fix some of the issues.  
  
- Once the issues above are fixed, our tests don't find any other issues (neither safety nor liveness), but only under strong **assumptions** 
(please note that this is not a strong mathematical proof, but just TLC model checker's  simulation tests).
    1. Lift Originator is not malicious.
    
    2. Non-originator nodes are not malicious (the only malicious thing that non-originator nodes can do 
    is to change the Lift value, and the protocol handles this situation properly).
    
    3. All nodes don't crash for infinitely long time, that is all nodes are eventually available and responsive.
    
    4. The network is partially synchronous, that is there are period of times when
     all messages can be delivered and delayed for not more than a known bound.
      
- [Option 1](#option-1) and [Option 2](#option-2) mentioned above allow to have a correct protocol (safety and liveness) 
without requiring one of the assumptions: 
    - with Option 1  we can remove assumption (iii)
    - with Option 2 we can remove assumption (i)
-  But we don't see any proven options on how we can deal with
 violation of any pair of the assumptions at the same time (See [Issues When Assumptions Are Violated](#issues-when-assumptions-are-violated)).
    - Please note that the options we propose don't have a strong mathematical proof.
    - We don't say that it's not possible at all to find a protocol which can deal with violation of 
    more than one assumption; we just don't see such options right now, so this is a place for more research.
    
### General Recommendations

- If the assumptions above (also taking into account [Protocol Options](#protocol-options-to-fix-the-overlift-issue-3))
doesn't look too strong for the first delivery, then we can proceed with the general implementation.
If the assumptions are too strong, then we need to think about how the protocol can be improved. 
    - Please note, that if later on we realize that assumptions are too strong and we need to 
    be able to violate at least two of them, then we may have to change the protocol a lot,
    which may require a lot of changes in the implementation as well.

- If it's decided that the assumptions are not too strong for now, the following needs to be taken
into account when working on the implementation:
    - The found issues in the current protocol and implementation must be fixed
    (see [Issues In The Currently Implemented Protocol](#issues-in-the-currently-implemented-protocol) 
     and [Issues In the Current Source Code](#issues-in-the-current-source-code)).
    - In particular, either [Option 1](#option-1) or [Option 2](#option-2) should be implemented. 
    - [Recommendations for the current protocol](#recommendations-for-the-current-protocol) should
    also be taken into account.
 
- We would recommend to have the next phase as a phase devoted to protocol improvements 
and think about [Making Assumptions Weaker](#making-assumptions-weaker).
This phase should probably be done by experts in distributed systems and consensus protocols 
(ideally, to have a mathematical proof of protocol correctness which can be published and reviewed by academics). 
If we have a phase like this, we recommend to 
    - analyze and think more about the current [Protocol options](#protocol-options-to-fix-the-overlift-issue-3) we have;
    - take into account [Recommendations for the current protocol](#recommendations-for-the-current-protocol);
    - explore the [Ideas for further research](#ideas-for-further-research).


## TLA+ Specification
TLA+ specification has been created for the Chit payment and Lift protocols:
- Chit payment positive case (as in `chit.png` diagram)
- Lift protocol positive case (as in `lift_success.png`)
- Lift cancellation cases (as in `lift_cancel_option1.png`)
- Malicious case when one of the non-originator nodes change the Lift value
- All the messages can be delayed up to some bound
- Messages can be received in a different order


## Issues In The Currently Implemented Protocol

### Issue 1: Invoice pend chits

 If a Stock uses the Pend state for an invoice which has not been paid by the Foil yet,
 then this may further lead to this node's overlift. 
 This is so because such a pending chit in the stock tally increases the Stock's projected balance.
 This allows participation in lifts which decrease the Stock's available balance below zero while keeping Stock's
 projected balance non-negative. Moreover, Foil can then reject the invoice or the invoice 
 can be timed out and this will leave the Stock's available balance negative on a longer term basis
 (at least until the next transaction in the network).

Note that pending chits associated with lifts decrease the Stock's projected balance. 
So they don't lead to such the issue.

**Example:**

- Cycle: A -> B -> C -> D -> A (downstream).
- C has 10 chips (both projected and available) on its stock tally with B and a debt -15 chips 
(both projected and available) on its foil tally with D.
- C sends an invoice for 5 chips to B and adds the Pend chit to its stock tally.
 Now the projected balance of C's stock tally with B is 15, its available balance is still 10.
- A originates a lift for 15 chips.
- C agrees to participate in the lift since the projected balances of both its tallies allow this.
Now the projected balance of C's stock tally with B is 0, its available balance is still 10.
- The lift is committed. Now the projected balance of C's stock tally with B is 0, its available balance is -5 
(**overlift which may be eliminated soon in case B pays the invoice from C**).
- B declines the invoice from C. Now both balances (projected and available) of C's stock tally with B is -5 (**overlift**).

**Solution:**  
Introduce another state for pending invoices (let's name it Invoiced) and do not consider chits in this state
when calculating a projected balance.

### Issue 2: Interlocking lifts

Two lifts originated by different nodes on the same cycle may block each other.
This case is not necessarily a deadlock but obviously reduces chances of circular lifts automatically
triggered by different nodes in a cycle to succeed.

**Solution:**

1. In case the node cannot participate in a lift due to the insufficient balance,
it must fail the lift explicitly rather than leave it hung up until the timeout.
This will reduce the period of presence of pending chits which are the cause of blocking other lifts.
This approach is represented by Case 1 in `lift_cancel_option1.png` and `lift_cancel_option2.png` diagrams.  
2. Logic of triggering circular lifts should be improved with addition of random delays which, 
taking into account the cycle length, will reduce the interlock probability.

**Detectable: Yes**

In general it's clear who initiated a lift. If there are two malicious colluded nodes
in the circle who block all other lifts from progress by sending lift proposals at the same time, other nodes 
will know the originators of both lifts (that is both nodes).

So, the direct peers (neighbors) of the malicious nodes can close the tallies with them.

Detection may require an algorithm to distinguish malicious actions and unintentional cases where
multiple honest lifts originate the lift around the same circle at the same time by chance.        

### Issue 3: Overlift in case non-originator node cancels timed out lift on its own

If in case of a lift timeout a non-originator node cancels the pending lift on its own,
then this may further lead to this node's overlift.
This may be so in case the node canceled a lift, committed a new one, and then 
received a final commit message for the already canceled lift.

**Example:**

- Cycle 1: A -> B -> C -> D -> A (downstream); Cycle 2: C -> D -> E -> F -> C
  (downstream)
- C has 10 chips (both projected and available) on its stock tally with B, 5
  chips (both projected and available) on its stock tally with F and a debt -10
  chips (both projected and available) on its foil tally with D.
- A originates Lift 1 for 10 chips (Cycle 1)
- C agrees to participate in Lift 1 since the projected balances of both its
  tallies allow this. Now the projected balances of C's tallies are: stock from
  B = 0 / stock from F = 5 / foil to D = 0.
- C does not receive any further messages related to Lift 1 in a specified
  period of time and so times out Lift 1 and the corresponding chits. So the
  projected balances of both C's tallies return to their initial values: stock
  from B = 10 / stock from F = 5 / foil to D = -10.
- D originates a Lift 2 for 5 chips (Cycle 2)
- C agrees to participate in Lift 2 since the projected balances of both its
  tallies allow this. Now the projected balances of C's tallies are: stock from
  B = 10 / stock from F = 0 / foil to D = -5.
- C receives Commit of Lift 2 and commits it. Now the projected balances of C's
  tallies are: stock from B = 10 / stock from F = 0 / foil to D = -5; the
  available balances of C's tallies are the same: stock from B = 10 / stock from
  F = 0 / foil to D = -5.
- C receives a belated Commit of Lift 1 and must to obey despite it has already
  moved Lift 1 record into Timeout state. Now the projected balances of C's
  tallies are: stock from B = 0 / stock from F = 0 / foil to D = 5
  (**overlift**); the available balances of C's tallies are: stock from B = 0 /
  stock from F = 0 / foil to D = 5 (**overlift**).

**Solution**

Either [Option 1](#option-1) or [Option 2](#option-2) can be implemented to deal with this.

The current TLA+ specification has Option 1 implemented and tested.
This is shown as Cases 2 and 3 on the `lift_cancel_option1` diagrams.

Option 2 is depicted on the `lift_cancel_option2` diagram.


## Protocol Options To Fix The Overlift Issue 3

### Option 1

This option is depicted on the  `lift_cancel_option1` diagram.

Instead of a policy when a non-originator nodes can cancel pending lifts on their own,
but at the same time must obey belated Commit messages,
use another policy: only the originator node can cancel the lift in case of timeout and it sends
a Timeout message upstream in this case.
Every other node must stay with the pending lift until it receives either Commit, Fail or Timeout message.

Option 1 allows non-originator nodes to ask the lift originator for the Final Commit if they didn't receive it 
from their neighbor peers.
This allows, in particular, to deal with the situation when some nodes around the circle are crashed or
not available for a long time.     

### Option 2

This option is depicted on the `lift_cancel_option2` diagram.
In this option all timeout, fail and cancellation messages can go in downstream direction only.

The timeouts are expected to be sent in downstream direction only to avoid 
the [Overlift Issue 3](#issue-3-overlift-in-case-non-originator-node-cancels-timed-out-lift-on-its-own)
when nodes decide to time out in a non-coordinated way.  

- When a node has already participated in the lift proposal, it can send Timeout message only 
if it is either originator or destination.
Otherwise it can only send a request about the lift status to its foil peer (upstream).
- Both Commit and Timeout messages are propagated downstream only.
- If a non-originator node receives a request about the lift status from its stock peer then:
  - If the node has Commit or Timeout message from its foil peer then it replies with it.
  - If the node has neither Commit nor Timeout then it forwards the request about the lift status to its foil peer (upstream).
   When it receives the reply, it forwards this reply to its stock peer (downstream).
  - If the node is the destination and it does not receive the reply from the originator in a specified period
   then it sends Timeout message to its stock peer (downstream) on its own.
  - If the lift is unknown for the node then it sends Timeout message to its stock peer (downstream) on its own.
- If the originator has received the matched Terminus in time, then it does not put the lift into Good state 
when sending Commit but puts it into Pre-commit state.
When the originator receives the loopback Timeout or Commit message from its Foil,
then it asks the lift destination (downstream) if it has the same lift state. 
If yes, then the originator commits or times out the lift.
    - If the originator doesn't double-check the lift state with the destination, a malicious foil 
    can cause safety issues.
    - For example, if the originator gets Commit from the Foil, it can be that the lift actually timed out 
    since the lift destination wasn't able to get a Commit message from the originator. 
    So, if the Originator commits the Lift, it would loose chips (pay to the Foil) without getting anything 
    back from the Stock (as it timed out the lift).   
    
Please note, that as the final commit phase goes in downstream direction only, 
this option assumes that all nodes are eventually available and can finish the lift around the loop.

The nodes can not ask the lift originator for the lift status, as they may get and apply a Commit message,
while other nodes upstream already decided to time out the lift.   

### Comparison of Option 1 and Option 2 behaviors

Option 1 and Option 2 behaviors are mutually exclusive.
The specification in TLA+ presented in this repository implements Option 1.
Each of these options has its pros and cons. They are listed below.

#### Option 1

**Pros:**

- Doesn't require assumption (iii) (see [Summary](#summary)).
Any node except the originator may crash or be unavailable for a long time.
The nodes can ask the originator directly about the lift's status and finish the lift.

**Cons**:

- Requires assumption (i). Otherwise the originator can block its proposed lift by sending neither Commit nor Timeout.
This can hamper other lifts because the pending chits associated with this lift reduce (in magnitude) projected balances of the nodes in the cycle.
See [Liveness Issue 5](#issue-5-liveness-issue-due-to-malicious-lift-originator).
- Requires assumption (ii). Otherwise an attack when the malicious originators send both Timeout upstream and Commit
downstream is possible. 
See [Safety Issue 6](#issue-6-safety-issue-due-to-collision-of-two-malicious-nodes).

#### Option 2

**Pros**:

- Doesn't requires assumption (i), so that it excludes the case when the originator blocks its proposed lift
 by sending neither Commit nor Timeout.
 However, the originator and destination together can still block the lift if they collude or the destination node 
 belongs to the originator as well.
- [Safety Issue 6](#issue-6-safety-issue-due-to-collision-of-two-malicious-nodes) is not possible here. 

**Cons**:

- Requires assumptions (ii) and (iii). No nodes (except the originator) may go offline in any proposal or commitment phases.

#### Trade-off

From the pros and cons of Option 1 and Option 2 it can be seen that Option 1 provides better liveness
while Option 2 provides better safety.


## Making Assumptions Weaker
As we've just seen, fixing the issues above doesn't remove a need for assumptions (i) - (iv) (see [Summary](#summary)).

[Option 1](#option-1) and [Option 2](#option-2) can help with removing one of the assumptions.  
But currently we don't see any proven options on how we can deal with violation of any pair of the assumptions (i)-(iv)
above at the same time.

##### Not requiring assumption (iv)
If we don't require assumption (iv), that is assume that the network is fully asynchronous, then 
we must require all other assumptions (i), (ii) or (iii) because of the [FLP Theorem](https://groups.csail.mit.edu/tds/papers/Lynch/jacm85.pdf).
In other words, it was mathematically proven that deterministic consensus is impossible in
asynchronous network even if just one node is faulty.

##### Not requiring assumption (iii)
By default we can not tolerate crash of even a single node around the circle,
which will lead to a [Liveness Issue 4](#issue-4-liveness-issue-due-to-crashed-nodes). 

There is an [Option 1](#option-1) on how to deal with it. It requires presence of the assumption (i), otherwise 
a [Liveness Issue 5](#issue-5-liveness-issue-due-to-malicious-lift-originator) can happen.
 
If assumption (ii) is violated in this option, then we may face breaking the safety property 
(overlift for some nodes) in the presence of just two maliciously colluded nodes.
See the [Safety Issue 6](#issue-6-safety-issue-due-to-collision-of-two-malicious-nodes) for details. 
 
##### Not requiring assumption (i)
If the Lift originator is malicious, then it can stop all other lifts around this circle
from progress by not sending a Final Commit and keeping the pending state on all the nodes in the Lift.
In other words, it breaks the liveness property (see [Liveness Issue 5](#issue-5-liveness-issue-due-to-malicious-lift-originator) for details).

There is [Option 2](#option-2) on how to fix it, but it works only under assumptions (ii) and (iii), otherwise
we may face breaking the liveness property the same way as in [Liveness Issue 4](#issue-4-liveness-issue-due-to-crashed-nodes).
  
  
## Issues When Assumptions Are Violated

### Issue 4: Liveness issue due to crashed nodes

Let's consider the following example: 
- Cycle: A -> B -> C -> D -> A (downstream)
- C has 10 chips (both projected and available) on its stock tally with B and a debt -15 chips
(both projected and available) on its foil tally with D.
- A originates Lift 1 for 10 chips.
- C agrees to participate in Lift 1 since the projected balances of both its tallies allow this.
Now the projected balances of C's tallies are: stock 0 / foil -5.
- A sends a final Commit
- Node B (downstream) is crashed
- As in order to finish the lift Node C needs to get a message (Commit or Timeout) from B,
it has to wait until B comes back online, which can be quite long period of time.
- Until this, as the Node C still has the pending lift and chits 
and the stock tallie's projected balance equal to 0.
So, it can neither finish this lift nor participate in any new lifts.   

**Solution:**

The issue can be fixed by either
- Requiring assumptions (ii) and (iii) (see [Summary](#summary)).
- Implementing [Option 1](#option-1) where Node C can get the Final Commit from the Node A (lift's originator)
and finish the lift.

**Detectable: Mostly Yes**

The direct peers (neighbors) of the crashed node can see the issue and close the tallies.
If [Option 1](#option-1) is implemented, then a node can ask the Lift Originator for the missing or delayed message,
and break the tally with the neighbour peer if it still can not get this message from it.    

However, the following may make it not so obvious:
- Distinguish crash of the node and network delays.
- Malicious nodes may delay the messages so that the delay is not long enough to break the tally, 
but quite significant for the general performance of the protocol.


### Issue 5: Liveness issue due to malicious Lift originator

A node can propose lifts but then neither commit nor time out them. This will hamper other lifts on this route
to succeed because of reduced (in magnitude) projected balances of the nodes in this route.

Let's consider the following example: 
- Cycle: A -> B -> C -> D -> A (downstream)
- C has 10 chips (both projected and available) on its stock tally with B and a debt -15 chips
(both projected and available) on its foil tally with D.
- A originates Lift 1 for 10 chips.
- C agrees to participate in Lift 1 since the projected balances of both its tallies allow this.
Now the projected balances of C's tallies are: stock 0 / foil -5.
- A never sends a final Commit
- The Node C (as well as B and D) still has the pending lift and chits 
and the Node C stock tallie's projected balance equal to 0.
So, it can neither finish this lift nor participate in any new lifts.   

**Solution:**

The issue can be fixed by either
- Requiring assumption (i) (see [Summary](#summary)).
- Implementing [Option 2](#option-2) where the nodes can time out the lift in a safe way without 
a need to rely on the originator.  

**Detectable: Mostly Yes**

The Lift destination who is the Lift Originator's Stock can see the issue and break the tallies.
If [Option 2](#option-2) is implemented, the Lift destination can create and propagate the Timeout message
to all the nodes downstream.  

However, the following may make it not so obvious:
- Distinguish crash of the node and network delays.
- Malicious lift originator may delay the messages so that the delay is not long enough to break the tally, 
but quite significant for the general performance of the protocol.

### Issue 6: Safety issue due to collision of two malicious nodes

This issue assumes that [Option 1](#option-1) is implemented, and, in particular,
the Case 3 from `lift_cancel_option1.png` where the lift originator can cancel the lift
by sending the cancellation message upstream if it doesn't get a Terminus on time. 

Let's consider the situation when two nodes collude and 
substitute the key, signature and a socket in lift messages for the segment of nodes between them.
They don't pass a lift Query out of the segment forcing the originator to cancel the lift. 
When the lift Timeout message reaches one of this node, the other one sends a fake Commit message
in the opposite direction.

In result some node within the segment receives Timeout from its stock peer and Commit from its foil peer.
So it gets loss and finds itself deceived but both its peers are honest and it is not easy to find out 
who is malicious.

Please note, that if the victim node chooses the Commit message (ignoring the Timeout), and propagates
the Commit further downstream, it may cause an overlift on downstream nodes the same way as in 
[Overlift Issue 3](#issue-3-overlift-in-case-non-originator-node-cancels-timed-out-lift-on-its-own). 

**Example:**

- Cycle: A -> B -> C1 -> C2 -> ... -> Cn -> D -> A (downstream).
- B and D collude.
- A originates a lift.
- D substitutes the A's key and socket by its own, and substitutes the signature by a new one
 created via its own key. The lift originator is not changed.
- D shares the new keys with B so that B can also sign the messages by this key. 
- D passes the altered Query upstream.
- The upstream nodes doesn't see any issues as they don't know what is the actual A's public key and socket,
and has no way to check if it's tampered. 
- So, all nodes between D and B participate in the lift proposal.
- When B receives this altered Query, it creates a pending chit in its foil tally only.
 B does not send Terminus to A.
- A does not receive Terminus in time and sends Timeout to D.
- D substitutes A's key, socket and signature the same way as during proposal phase.
- D notifies B about this and passes the altered Timeout upstream.
- B receives the notification from F, and creates a fake Commit signed by the altered keys.
- B sends the fake Commit downstream, pretending that it is issued by A,
and moves its sole pending chit to Good state. So **B gets profit**.
- Some node Cm where 1 < m < n receives Timeout from its stock peer and Commit from its foil peer.
So **Cm gets loss** and finds itself deceived but both its peers are honest and it is not easy to find out who is malicious.

**Solution:**

The issue can be fixed by either
- Requiring assumption (ii) (see [Summary](#summary)).
- Implementing [Option 2](#option-2) where Timeout is sent downstream only and not upstream.  

**Detectable: No**

The victim node Cm (1 < m < n) is not a direct neighbour of malicious nodes D and B and has no information about them.
The Lift originator is also anonymous for the node Cm.
 

## Issues In The Current Source Code

#### Lack of signatures

Signatures are not actually used in the current code.

#### peerValid is sent before the chit is applied to the chain

On `userAgree` request, the `peerTransmit` of `peerValid` action is done before update
of the chit's status to `Good`, which means that the Foil doesn’t have the `chain_idx` assigned 
to the chit yet, and hence the `chain_idx` is not transferred to the Stock.
So, upon receiving the `peerValid`, the Stock also doesn’t have the `chain_idx` and will use 
its own order. This may cause inconsistency between Foil and Stock.

A simple solution is to update the chit's status by the Foil before sending the peerValid action.

#### Issues with docker run

It's not possible to run the simulation in docker without local installation.
 
The fixes are attached.

#### Check chit chains for consistency

Currently there are no checks that Foil's and Stock's chit chains (pairwise microledgers)
for the given Tally are consistent.

- chit chain root hashes needs to be compared
- need to check that the Stock got all records from the Foil (no gaps in `chain_idxs`) 


## Recommendations For The Current Protocol

#### Consider a cyclic lift as a subcase of a linear (originator = destination)

Consider a cyclic lift as a subcase of a linear lift where the originator and destination are equal.

With this approach, a circular lift will occur in the following way:

- Let's A be a both the originator and the destination
*(the originator and the destination are the same for a circular lift with this approach)*.
- In the beginning of the proposal phase, A as the originator creates the lift record in Seek state,
creates a pending chit in its stock tally only and sends Query to its foil peer.
- When A receives Query as the destination from its stock peer,
it creates a pending chit in its foil tally (note that A already has the lift record in Seek state)
and sends Terminus to itself as the originator.
- [...the proposal phase is being done in the usual way...]
- When A receives Terminus as the originator, it verifies Terminus message for equality
to its original lift record and, if they match, it commits the lift record,
commits the pending chit in its stock tally and sends Commit to itself as the destination.
- When A receives Commit as the destination, it commits the pending chit in its foil tally
(note that A's lift record is already in Good state) and sends Commit to its stock peer.
- [...the commitment phase is being done in the usual way...]

#### Separate Tallies for Foil -> Stock and Stock -> Foil

For bi-directional payments between nodes X and Y we recommend to use two tallies
(and hence two chit chains or pairwise microledgers):

- X as Foil -> Y as Stock
- Y as Foil -> X as Stock

With this approach payments will always be done from Foil to Stock while lifts will always be done from Stock to Foil.

This should be done for the following reasons:
- Simplify further development.
- Greatly reduce a risk of inconsistency between the Stock's and Foil's chit chains. 
We may even not need a consensus protocol for the Foil and Stock chit chains in this case. 
- Simplify a possible audit.

#### Combine `request` and `status` fields in implementation
Currently there are two separate fields representing the current state of a Lift or Chit state machine:
`request` and `status` (see also `lift_state` function in the source code).

It would be much more clean, clear, readable and less error-prone to combine them into just one `state` field.

The current diagrams (`diagrams` folder) are an example that this is possible. 
There we use just one `state` field which is a combination of `request` and `state`. 

## Ideas For Further Research

#### Ideas to get rid of assumptions (i), (ii) and (iii) at the same time
If we want to get rid of assumptions (i), (ii) and (iii) at the same time (see [Summary](#summary)),
that is to work in a presence of the both malicious and crashed nodes, we may need to 
do quite significant changes in the protocol to tolerate some number of crashed or byzantine nodes, 
or make the possible issues detectable for the victim.   

- **Option A**: Arbiter nodes establishing trust for the lift
  - The system may have multiple Arbiters
  - The nodes participating in the lift need to agree to deal with the proposed arbiter for the lift
  - Arbiter can be used to propagate Final Commits and Timeouts    
  - Arbiter can be used to get missing lift messages 
  - We have to assume that Arbiter is never malicious and 24/7 available. 
  - We need to introduce reputation and trust for Arbiters.
  - A blockchain can be used as a decentralized Arbiter.  
- **Option B**: Consider traditional consensus protocols for the Final Commit phase only or for the both Conditional and Final Commit Phases.
This may weak the [assumptions](#summary) a lot allowing to have up to 1/3 nodes be crashed or malicious (byzantine failures). 
    - May require a different communication pattern (every pair of nodes can communicate with each other in a peer-to-peer way).
    - Consider keeping a pairwise ledger for payments, but have a global ledger(s) for Lifts
    - The following protocols can be considered:
        - [PBFT](http://pmg.csail.mit.edu/papers/osdi99.pdf)
        - [Tendermint](https://docs.tendermint.com/master/introduction/what-is-tendermint.html#consensus-overview)
        - [HotStuff](https://www.cs.unc.edu/~reiter/papers/2019/PODC.pdf) or [Facebook Libra](https://developers.libra.org/docs/crates/consensus)
        - [Stellar](https://www.stellar.org/developers/guides/concepts/scp.html)
        - [HoneyBadger](https://eprint.iacr.org/2016/199.pdf)       
    - Consider best practices for inter-blockchain or inter-ledger communication:
        - [IBC](https://tendermint.com/ibc/)

#### Ideas to get rid of the both assumptions (ii) and (iii)

If we want to get rid of the both assumptions (ii) and (iii) (see [Summary](#summary)), that is to 
work in a presence of the both malicious and crashed nodes (except the originator), we may implement [Option 1](#option-1)
and find a way to deal with the [Safety Issue 6](#issue-6-safety-issue-due-to-collision-of-two-malicious-nodes).

In order to do this, we need to either find a fix for the issue, or at least make it detectable for the victim nodes.
We may try to bind the identity of the nodes (lift originator in particular) to the public key and the socket
to make it detectable:
- **Option A**: Arbiter nodes establishing trust for the lift (see above)
- **Option C**: Blockchain containing IDs of all nodes with the corresponding public keys
  - See [Hyperledger Indy](https://www.hyperledger.org/use/hyperledger-indy)
  - See [uPort](https://www.uport.me/)
- **Option D**: PKI system with Certification Authorities binding the originator's entity to the public key.
- **Option E**: Introduce a reputation system to reduce probability of malicious actions
  - Consider using a blockchain as a reputation system.  
  - The reputation approach can reduce the probability of some issues and overlifts,
    but it may have the following potential disadvantages that need to be taken into account:
       - Not being able to initiate a lift for a user without a good reputation looks like
       a serious UX issue. For example, a new user can not do a linear lift in order
       to buy something in the online shop.    
       - A malicious actor may behave correctly for a long time, and got very good reputation.
        But then it suddenly does the  [Safety Issue 6](#issue-6-safety-issue-due-to-collision-of-two-malicious-nodes) attack.
        It will affect its reputation, but not always dramatically because of the following:
            - Its neighbor partners are not affected by the attack.
            A random node far from the attacker is affected, and initially only this node decreases
            the reputation.
            - So, the affected node needs to propagate the lose of the attacker's reputation somehow.
            The propagation may be blocked by some non-affected nodes colluded with the attacker.
            In any case, the reputation needs to be managed in non-individual way and propagated to other nodes.
            - Even if the lose of reputation is propagated, it may be OK for the attacker:
                - The attacker may not be interested in these tallies anymore.
                He got the benefits, and can close the tallies.
                - The attacker may have multiple keys/sockets with a good reputation.
                Even if one of the pairs is compromised, the other one can still be used for the lifts.

#### Ideas to repair a broken lift (overlift)
We may think about a way to recover from a breaking safety property
(for example an Overlift as in [Overlift Issue 3](#issue-3-overlift-in-case-non-originator-node-cancels-timed-out-lift-on-its-own)).

Even if it's possible to find such a recovery protocol, this approach has the following disadvantages:
- Even a short violation of a safety property (for example an overlift) can be noticed by the user
which leads to a very bad UX. For instance, the user may get useless coupons (more than he or she wanted)
as a result of a lift.
- It can be that recovering is not possible for quite a long time, which increases the probability that the issue
is noticed by the user. 

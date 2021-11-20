## Thoughts on Future Direction
Written July 2020

### Context (Fall 2021):
This was written after the [DSR testing](/test/analysis/dsr), but before the
[revised protocol](learn-protocol.md) was designed and documented.
The Transaction Manager mentioned below was boiled down to the concept of
a Referee mentioned in the new protocol.
This [appears to be](/test/analysis/byu) the minimal amount of centralization 
necessary to produce a live and safe result

### Lessons Learned:
The original demonstration code for the lift algorithm was written without 
fully understanding how it would turn out.

Admittedly, that is not an ideal development path.  But in my case, taking an 
initial pass at coding was necessary to my understanding the problem well 
enough to be able to properly design it--kind of a chicken/egg problem.

I had the theory of what I was trying to accomplish from an accounting and 
economic standpoint.  And I knew the objectives I wanted to achieve.  But I 
wasn't quite sure how (or even if) a lift could be performed in a completely 
distributed way.

In any case, the coding exercise was useful as it created a platform for 
visualizing the complexity happening below the surface in a credit lift.  And 
it made it possible for me to articulate the problem well enough for the DSR 
study to even take place.

That study was a huge learning experience.  Most notably, it helped me discover
analysis tools (such as TLA+) that can shake out the bugs in the algorithm 
before even attempting to make the next coding pass.

Going through the TLA+ tutorial was helpful just to see how others have dealt 
with achieving consensus in a distributed network.

### The Central Problem:
It would appear there is no perfect way to guaranty both safety and liveness in 
a fully distributed, and de-centralized network.  There are algorithms for 
achieving consensus (Two-phase commit) but they rely on some authority 
(Transaction Manager) to arbitrate the results of the final commit.

And even the Two-phase commit algorithm has its potential problems.  We have to 
rely on the honesty and the integrity of the Transaction Manager (TM).  If that 
node goes down in the middle of the transaction, we can be left in an 
inconsistent state.  Leslie Lamport, the author of TLA+, has proposed the Paxos 
Commit algorithm which makes this process much more robust by using multiple 
TMs and hoping at least a majority of them remain reachable through the 
transaction.  That would likely provide the consistency MyCHIPs needs as long 
as the issue of de-centralization can be solved.

https://lamport.azurewebsites.net/video/consensus-on-transaction-commit.pdf

De-centralization is critical to the success of MyCHIPs.  If there is any 
company, agency, database, or other ultimate authority at the center of a 
system, it will ultimately become the target of some kind of corruption and/or
attack.  That may come from those who do not want decentralized money to 
succeed, or it may just be an effort to coopt the system for personal gain.  
Either way, the goal of MyCHIPs is to avoid all that and make a reliable 
system regular (i.e. honest) people can use by themselves and for themselves.

### A Proposed Solution:
So what if we resolve to use a TM (i.e. a bit of centralization) for each lift, 
but have the protocol allow for anyone to become a TM?  The idea is: the lift 
initiator would propose a node it would like to use as TM for that lift.  Each 
node along the lift chain could decide if it trusts the proposed TM (identified
as a socket address and public key) or not.  Participation in the lift is
always voluntary.

If the originator chooses a well known and trusted node as TM, it is more
likely to get the participants it needs for the lift.  In fact, nodes could 
return a special code if they opt out of the lift purely because the proposed 
TM is not acceptable.  That would be a good signal to perhaps try again with a 
better recognized TM.

A further enhancement would be to allow sites to execute trading tallies with
a number of TMs.  TMs could, for a fee, offer lift insurance, payable through
those tallies.  The TM would guaranty not to leave the site in an inconsistent 
state.  And if it did, it would provide a pathway for a followup lift to heal 
the imbalance of the resulting broken lift.  If a TM site holds a tally with 
each party (site) to the lift, it should be able to formulate a fixup lift, 
after-the-fact, to cure any inconsistency at no real cost to anyone (just 
making sure all the credits and debits cancel out).

Summary of Objectives:
  - There can be any number of nodes in the network willing to serve as TM's
  - It will be up to them to develop their own reputations of trust
  - Each site can determine who it finds trustworthy enough to be TM
  - In addition to TM services, nodes can offer lift insurance
  - If a site gets lots of lift requests for a particular TM, not in its
    list of trusted TMs, it might want to consider establishing a 
    relationship with the new TM.
  - Objectives:
    - There is no singular authoritative (central) system of trust.
    - Parties decide on their own who to trust.
    - Traders decide who to establish tallies with (partners).
    - Sites decide who to trust to perform lifts (TM's).
    - Liveness:
      - All lift transactions are guaranteed to terminate (Paxos or other
        similar Commit) either as a commit or a cancel.
    - Safety:
      - Sites guaranty their users lifts that will safely clear their credit.
      - Sites guaranty to each other to act honorably when designated as TM.
      - Malicious actors can harm only themselves or their adjacent partner.
      - Malicious transactions can be discovered and documented.
      - All parties to a lift reach consensus about the commit/cancel.
      - If that fails, insured transactions are at least repaired.

<br>[Next - FAQ Libraries](ref-faq.md)
<br>[Back to Index](README.md#contents)

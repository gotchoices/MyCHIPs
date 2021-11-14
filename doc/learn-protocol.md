## MyCHIPs Protocol Description 1.0 (draft)
July 2021; Copyright MyCHIPs.org

### TODO
- Show message class/object diagrams for each protocol?
- Expand state machines to handle retries?
- Update to protocol 1.0 features
- Lift chits signed by referee now

### Overview ([TL;DR](#network-assumptions "Skip to the meat"))
As the project began, it was difficult to attempt a top-down design of the system.

I had a basic, intuitive idea about how sites and nodes should communicate with each other,
and what types of messages they would send back and forth, but I didn't really understand it
in a formal enough way to create a detailed description of the protocol.
Instead, I jumped in and started coding.

While that is probably not the most widely accepted approach, it did give me a working prototype of a MyCHIPs site, albeit not yet secure.
In conjunction with the agent-model simulator, I could generate random data sets.
And with the network visualizer, I could now actually see what a network might evolve into and what type of scenarios the protocol would have to handle.

As I went, I produced documents like those included here for
[tallies](Tallies.md) and [lifts](Lifts.md)
to help me make sense of what I needed to code.
Those still serve as a helpful reference for the prototype implementation.

Next came the DSR study, which revealed some security/liveness flaws in the way I had designed and implemented the protocol.
The intermediate BYU results (as of Summer 2021) indicate that the addition of the referee will now allow a distributed lift that is acceptably live and secure.

Admittedly, the referee is a compromise from the original goal of a fully distributed system.
But it is still highly decentralized, and its main role is so nodes can achieve consensus about when a pending lift should expire.
Thankfully, the referee doesn't need to know anything about individual entities' balances, keys, or other sensitive data.
So all other functions are still fully distributed.

This document is an attempt to more formally describe a refined protocol with the help of UML sequence and state diagrams.
The goal is to prepare the way for a further revision of the codebase to bring it into line with this improved protocol.
Hopefully this will serve as a clear enough description that any eventual implementation can interoperate with any other.

### Network Assumptions
MyCHIPs assumes a network of peer entities who become interconnected through voluntary credit relationships they establish with each other.
Such an entity could be an individual person or it could be a legal organization such as a corporation or a partnership (i.e. a group of people).
The term *user* is also used to be roughly synonymous with entity (with a possible bias toward human entities).

Entities should quantify the degree to which they trust the peer entities they connect with.
When that trust is greater than zero (i.e. [credit terms](./Tallies.md#credit-terms) are offered), one should be prepared to lose the amount of value quantified in the trust.
For example, if I extend you 10 CHIPs of credit, I must recognize the possibility that you may fail to uphold your promise.
In that case, I may lose the promised value, or have to rely on collateral if such is a part of the particular credit agreement.

Although this limited risk from trading parters is a necessary part of the system, people should not be exposed to indirect risks.
For example, if I (A) share a tally with you (B), and you also share a tally with a third entity (C), I don't want to have to rely on your trust of C.
C may hurt you.  But I don't want C to be able to hurt me.

So the assumptions in a distributed network are that contracts and obligations exist only between two immediately connected peer entities.
The instrument for documenting and enforcing that connection is the [Tally](./Tallies.md).

### Sites and Nodes
When reasoning about lifts and other MyCHIPs transactions, it is sometimes easiest to think of entities as individual, independent nodes
in a giant [graph network](https://en.wikipedia.org/wiki/Graph_theory).

While this works pretty well in most cases, it is important to remember the implementation reality:
Individual entity accounts must be hosted on a server that can maintain a network presence at all times--even when a user's mobile device might be turned off.
And these servers will most likely host more than one user.

[![MyCHIPs Site](uml/scaling.svg)](uml/scaling.svg)

This introduces the notion of a *site* which typically represents a single database of users surrounded by a possible cluster of process and control-layer support servers.

The term *node* will get used in a more generic way, possibly referring to an entity, a site, or a set of users (a <i>segment</i>) within a site, depending on the context.
The term *server* may be used sometimes as roughly synonymous with *site.*

### Protocol Layers
This document is defining the **protocol** whereby nodes communicate with each other to:
- Establish tallies (formalized trading relationships) between entities
- Send value via direct Chits on a single tally
- Discover potential lift pathways through the network
- Execute distributed lifts across the network

In addition, we will cover the following which might be considered as sub-protocols:
- Gaining consensus between two entities sharing a tally as to the order of chits on the tally
- Communicating with a Referee nominated to call time on a lift transaction

At a lower level, sites will communicate with each other over an encrypted secure connection which uses
[Noise Protocol](http://noiseprotocol.org) and is discussed in some more detail in [this document](/doc/Dialogs.md).

### Tally Use Cases
A tally is established when two parties decide to formalize a relationship of trust between them using the MyCHIPs protocol.

![use-tally](uml/use-tally.svg)

Here is some additional detail pertaining to these four use cases:
- **Be My Vendor**:
  The User reaches out to a potential trading Partner and asks if he would like to establish a tally.
  This must alway happen via some communication channel outside the MyCHIPs protocol.
  We will call this “out-of-band communication.”
  Examples include meeting in-person, email, teleconference or a traditional web connection.
  In this case, the User is suggesting he hold the [Foil](Tallies.md#tally-parts) of the tally and the Partner will hold the [Stock](Tallies.md#tally-parts).
  The partner is the vendor, or provider of services, so money (value) will normally flow from User to Partner.
  In the moment of exchange, the User will owe value to the Partner.
  In other words, the Partner will have lent money to the User.
- **Be My Client**:
  This is really identical in all respects to the previous case, except the User is suggesting he be the Vendor (the Stock holder) and the Partner will be the Client (the Foil holder).
- **Transaction**:
  Once established, the tally will serve as a foundation for actual trades, or pledges of credit.
  It will maintain and track a total balance owed in one direction or another.
  And it constitutes a digital signed contract indicating the [terms and conditions](Tallies.md#credit-terms) by which the two parties have agree to conduct their trades.
  The tally balance is modified by entering individual atomic transactions called [chits](https://www.dictionary.com/browse/chit).
  These chits are also digitally signed and become a part of the tally.
- **Request Close**:
  A tally must be completely voluntary on the part of both parties.
  However, once agreed to (signed), the entities are duty-bound to uphold its terms.
  So a tally can be closed at any time, but the obligated entity (debtor) must somehow bring the tally balance to zero.
  This might involve a [credit lift](Lifts.md) or it could be done by giving product, services, or some other kind of money.

### Tally Protocol
The steps to establish a tally are shown in the following sequence diagram.
This covers the first two tally use cases, the only difference being which entity is designated as the stock holder and which is the foil holder.

![seq-tally](uml/seq-tally.svg)

As mentioned, transactions are carried out as chits, which get added to the tally.
More on chits [below](#chit-use-cases).

When one of the partners wishes to end the trading relationship, he can do so by the steps in the following sequence diagram.
If the creditor wants to close the tally and is willing to forfeit his balance owed, he can simply gift the balance back to the debtor.
The tally, marked as "closing," will then close automatically.

If the creditor wants to retain what is owed to him, he will have to wait for the agreed upon payment terms to time out.
In the normal course of time, payment should be made by the debtor by way of a lift, or some other consideration of product, services or some other kind of money.

If the debtor wants to close the tally sooner, he will have to figure out how to provide value sufficient to zero the balance.

![seq-tally-close](uml/seq-tally-close.svg)

Now we can derive the following state diagram to describe the tally protocol from the perspective of a single entity:

[![state-tally](uml/state-tally.svg)](uml/state-tally.svg)

### Chit Use Cases
A chit constitutes a pledge of future value from one entity to the other.
There are two basic types of chits:
- **Direct Chit**:
  This is a simple chit issued by one entity, to its direct trading partner.
  This type of chit only needs to be signed by the entity pledging value.
- **Lift Chit**:
  In this case, the chit is part of a larger [credit lift](Lifts.md).
  There will be a whole group of chits, all bound to the lift.
  A lift chit will to be signed by a *site* certificate, where the site is the system that hosts the MyCHIPs account for the particular user.
  Clearly, the idea of letting one's Chip Service Provider sign chits on one's behalf sounds potentially dangerous.
  So there are some limitations on lift chits:
  - The net effect on an entity of a group (typically 2) of chits, belonging to a single lift, must be in accord with the [trading variables](Lifts.md#trading-variables) established and signed by that user.
  - In general, this means the chits sum to zero.
  - It could be non-zero if the trading variables specify a charge or allow a penalty.

![use-chit](uml/use-chit.svg)

This diagram shows two sets of similar use cases.
In the simpler case, we are negotiating a chip with a direct trading partner.
In the more complex case, we are executing a linear lift that will transmit value through the network to a peer we are not directly connected to.
This lift will also involve one of our direct partners who will be the first link in a chain of entities the lift will flow through.

### Direct Chit Protocol
We will first deal with the simpler case where a single direct chit is being entered onto an existing tally between two entities.
Either entity can make a direct payment to the other simply by making and signing a chit.

This diagram shows the first case, Sending a Direct Payment:

![seq-chit-pmt](uml/seq-chit-pmt.svg)

When requesting a direct payment from the other party, the sequence gets a little more complicated.
This involves the generation of an *invoice,* or request for payment:

![seq-chit-inv](uml/seq-chit-inv.svg)

This diagram also covers the fourth use case, Pay Direct Invoice.
This is what the Payor does once he receives the proposed chit (see the alt conditional block in the previous diagram).

Note that the [consensus algorithm](#consensus-protocol) has nothing to do with the validity of a chit.
If a chit is signed by the party pledging value (debtor), it is a valid chit.
However, the parties do eventually need to agree about the *order* in which chits are entered into the tally.

This is important from an implementation standpoint because the list of chits will be maintained as a [hash chain](https://en.wikipedia.org/wiki/Hash_chain).
This *chit chain* can be thought of as a tiny blockchain, known only to the two entities who share the tally.
When the data is kept this way, it is very easy for the two partners to verify that they have identical information, just by comparing the hash they hold for the last consensed chit on the chain.

The third use case (Request Direct Invoice) is one step before this.
For example, say you recognize that a vendor has provided services to you and you want to send payment.
You may not know the exact charge, but you want to initiate the process by Requesting a Direct Invoice.

This is not strictly part of the MyCHIPs protocol.
Rather it would be conducted as out-of-band communication (paper, http, email, or text).
But the software needs to facilitate the process by issuing/scanning QR codes containing the necessary data to initiate a responsive chit or lift.

For example: “Hey, how much do I owe you for that gopher-bomb?“
“Well, here's a QR code that will take you to an https endpoint that yields a JSON object containing just the information you are asking for!”

The returned object would contain:
- The address of the entity who will receive the payment (smoke-em-out@chippies.net),
- The amount payable,
- An optional listing and descriptions of items contributing to the total,
- Optional hints about where to find this entity on the network.

This sequence will be dealt with in more detail in the section below on [lifts](#lift-protocol).
It can be generalized to the simpler case above where an invoice is requested from a direct partner.

Now we can derive the following state diagram to describe the direct chit protocol from the perspective of a single entity:

[![state-chit](uml/state-chit.svg)](uml/state-chit.svg)

### Credit Lifts Explained
So far, the protocol has dealt primarily with transactions moving value between two partners who are directly connected by a tally.

Transactions of this kind are quite limited.
Certainly, one party can pledge value to another.
But so far, there is no obvious way to resolve such pledges (i.e. get paid) other than hoping for some later return of compensatory product, services or alternative money.

But MyCHIPs accomplishes much more than that.
It allows parties to transmit surplus credits (pledges) they hold, back through the network, and have them reappear as credits on other tallies where they can be spent on something you actually need or want.

The [lift algorithm](http://gotchoices.org/mychips/acdc.html) is like a way to “pay your bills” without the need for traditional money.
It can be thought of as trading what you *have but don't need*, for what you *need but don't have*.
This is sometimes called a “clearing function” as it “clears out” or “nets to zero” offsetting credits on each node it traverses.

<p align="center"><img src="figures/Lifts-1.jpg" width="500" title="Visualizing a lift with four participants"></p>

This figure shows a circular loop of trading partners.
The arrows show the normal flow of money, credit, or IOU's in a clock-wise direction.
Each arrow also represents a tally, pointing from the foil at its tail, to the stock at its head.

A circular credit lift will move value in the opposite, or counter-clockwise direction, clearing out credit imbalances along the way.

The linear version of the credit lift performs a related function, allowing you to send value through the network to an entity you are not directly connected to.
It can be thought of as paying with *what you have but don't want*, while the receiver gets *what he wants but does not yet have*.
Participating entities along the way also get the benefit of a clearing function on their own tallies.

<p align="center"><img src="figures/Lifts-2.jpg" width="400" title="A lift to transmit value"></p>

In order to perform these lifts, nodes must have some idea of where to send credits so they will arrive at their intended destination.
If there was a single, giant database of all the tallies in the world, this would not be such a difficult task.
A central-planning algorithm could simply determine the most efficient lift pathway and create the required chits on all the applicable tallies in a single, consistent, atomic transaction.

But MyCHIPs is purposely designed as a <a href="https://blockchainengineer.com/centralized-vs-decentralized-vs-distributed-network/">fully distributed</a> system.
The intent is, no single database will contain knowledge of the whole network.
Ideally, databases will only contain information about the *local* entities they host and other *foreign* entities their local users are directly connected to by tallies.
Even then, information about foreign entities will be kept as limited as possible.

To accomplish this, each database will build a map of theoretical routes believed to exist somewhere in the outside network.
For the purposes of regular (circular) lifts, the goal is to find external routes:
- from known, up-stream foreign entities,
- to known, down-stream foreign entities.

Knowing such external pathways, a site should be able to combine them with known, internal segments of entities to form a complete lift circuit.

<p align="center"><img src="figures/Lifts-3.jpg" width="400" title="A distributed lift"></p>

For linear (payment) lifts, the process is similar.
The goal is to find external pathways:
- from a known, up-stream foreign entity,
- to a particular, identified foreign entity,
- who may also have provided *hints* about one or more well-known entities it has a direct down-stream connection to.

We use the terminology *up-stream* to denote a peer who owes us excess money.
This is typically associated with a tally of which we hold the stock.
But it is also possible to accumulate excess CHIPs on a tally foil.
An employer or customer is a good example of a partner you would normally find up-stream from you.

We use the terminology *down-stream* to denote a peer we might owe money to.
Alternately, it could be someone who owes us less than we want them to.
This is often associated with a tally of which we hold the foil.
But it is also possible to have fewer CHIP credits than we want on a tally stock.
A merchant or supplier is a good example of a partner you would normally find down-stream of you.

<p align="center"><img src="figures/Lifts-6.jpg" width="500" title="Sites contain multiple users"></p>

This figure shows a convenient way to visualize a lift pathway in a real implementation.
A site database will contain multiple entities who are connected in a short, linear segment.
Some of these are local, meaning their accounts are hosted by the site.
For example, site B hosts users B1, B2 and B3.

Hopefully, each chain will also include two or more foreign users (hosted by some other site).
Otherwise, a distributed lift through the segment will not be possible.
For example, the chain [B1, B2, B3] is also connected to an up-stream foreign peer A3 at its top end
and a down-stream foreign peer C1 at its bottom.

Site B knows about a complete segment [A3, B1, B2, B3, C1].
But that is where site B's direct knowledge about the network ends.
It will be reliant on site A, site B, and probably a bunch of other sites to execute a complete distributed lift.

A lift segment is defined as:
- One or more local entities connected in a linear chain; and
- A foreign entity at the top of the chain; and
- A foreign entity at the bottom of the chain.

The *lift capacity* along a segment is computed by comparing the ability/desire of each entity in the chain to perform a lift.
Individual entities define [trading variables](Tallies.md#trading-variables) that control how many credits they would like to maintain on any given tally.

<p align="center"><img src="figures/Lifts-5.jpg" width="400" title="Computing lift capacity"></p>

The software compares the actual tally balance to the *desired* balance to arrive at a lift capacity.

### Route Discovery Protocol
Having identified local segments that have capacity for a potential lift,
each site then needs a way to cooperate with peer sites to gather just enough information so it can reasonably initiate lift proposals where needed.

Each site needs to know whether a potential external route exists where:
- a lift can be initiated through the top of a local segment (A3); and
- that lift will return to us via the bottom of the segment (C1).

Site B doesn't really need to know many details about the route--just whether one or more such paths exist.
The route may pass through many other sites on its way back to C1.
In fact, it may pass through some sites more than once, traversing multiple segments.

Now that site B has identified the local entities [B1,B2,B3] as a single segment with a known lift capacity, it can treat them as a single *node* in the lift--almost as though it were a single entity.
The lift will be committed (or canceled) in a single, atomic transaction on behalf of all the nodes belonging to the segment.

Route discovery requests can be initiated in two ways:
- Manually by a user/entity; or
- By an autonomous process acting as *agent* on behalf of the entity (such as a [CRON](https://en.wikipedia.org/wiki/Cron) job.)

![use-route](uml/use-route.svg)

An entity would typically request a route because it intends to make a payment (linear lift) to some other entity.
The payee entity's endpoint ID would typically be obtained by scanning a QR code.
The User Interface would send that information (and any hints) to his host site.
The server process can then commence the discovery process for suitable external routes to complete the intended lift.

Note: for a linear lift, each end of the lift will involve a *half segment*.
The payor node will consist of a local entity with zero or more other local entities upstream of it, and topped off by one foreign entity.
For example: [B3, C1, C2].

The payee node will consist of a local entity with zero or more other local entities downstream of it, and a single foreign entity at the bottom.
For example: [A2, A3, B1].

Nodes along the way get the same experience whether the lift is circular or linear.

![Manual Routing](uml/seq-route-man.svg "Manual initiating a route search")

As mentioned, an autonomous agent process is continually scanning for liftable balances along local segments.
Upon discovering a segment with a capacity for a lift, the system will check its database for possible external routes that can be used to complete the circuit.

![Automatic Routing](uml/seq-route-auto.svg "Automatic route scanning")

If a suitable route is not yet known, the agent will commence a search.
This is done by creating a draft route record in the local database and then propagating the query upstream.

If previous successful searches have been conducted, but are too old to be reliable, a new search should be initiated to freshen the route in the database.
This is done by resetting the local record to draft state and again propagating a query upstream.

If previous searches have been inconclusive, the agent should similarly retry after a reasonable amount of time has passed.

As mentioned, each site acts in two roles:
- It may initiate route queries necessary for conducting trades for local users; and
- It may receive queries from downstream and act upon them.

This second role is explained by the following sequence diagram:

![Routing Relay](uml/seq-route.svg "Responding to route queries")

Now we can derive the following state diagram to describe the route discovery protocol from the perspective of a single site:

[![state-route](uml/state-route.svg)](uml/state-route.svg)

### Lift Protocol
Once a site has discovered one or more viable external routes, it can proceed to propose an actual lift.
The proposal is sent out via an upstream foreign peer at the top of the subject segment.
This use diagram shows five possible phases of the resulting lift:

![use-lift](uml/use-lift.svg)

Here is the simplified example lift circuit again for reference.
Remember, each node could represent a single user or a segment of users local to a particular site.
We will consider node A as the lift originator.
Node B will be considered the destination of the lift.

<p align="center"><img src="figures/Lifts-1.jpg" width="500" title="Visualizing a lift"></p>

For a linear lift, just imagine the tally between A and B does not (or need not) exist.

#### Proposal

Proposals will travel counter-clockwise, <b>against</b> the normal flow of value (the arrows).
Node A will propose the lift to node D because:
  - Node A contains a route record indicating that an external pathway exists (or has existed) leading from node D, upstream and eventually to node B; and
    - it has capacity for a circular lift through an internal segment with D at the top and B at the bottom; or
    - it needs to transmit value from A to B (linear lift).

  The lift proposal is a conditional contract of the form:
  "If I send a specified value to you on this tally, you agree to send that same value along through another node you are connected to, with that value eventually reaching my intended destination."
  - The proposal contains a time, indicating how long the lift proposal will stay alive, before it will time out and will be considered "expired" (and therefore void).
  - It also contains the identity of a proposed referee whose job it is to declare when the lift time has expired (or certify its successful completion).
    The referee is typically a well known, reliable site that is reachable by any node on the network.
    Its identity consists of its
    - network address (domain name or IP number), and
    - (optional) network port
  - It is each site's responsibility to decide for itself what referees are worthy of trust, and to collect a public key (out of band) for each referee it chooses to rely on.
  - If node D wants to participate in the lift, on the proposed terms, it indicates this by forwarding the proposal along to node C where the process repeats itself.
  - This action makes the lift binding upon D, subject only to receipt of an authorizing signature, generated within the specified timeout, as judged by the named referee.
  - If/when C receives the validating signature (by any means), D's obligation to C becomes valid and provable, regardless of whether D cooperates further in the transaction.
    So every node has a natural incentive to cooperate in the second phase of the lift.
    If they don't, they will lose value to their upstream connection without recapturing it from downstream.

![seq-lift-prop](uml/seq-lift-prop.svg)

#### Confirmation, Ratification, Commit
  As long as a suitable route exists, the lift proposal will eventually reach its intended destination, or <i>terminus node</i>.
  The terminus node will communicate a confirmation directly to the originator to indicate that the lift has successfully propagated through its intended circuit (or linear path) and is ready to commit.
  The lift header contains a network address and port where the originator can be reached for this purpose.

  Once the originator has obtained the confirmation, it can decide whether it wants to proceed to commit the lift.
  But it can only do so if the time, originally set forth in the lift proposal, has not yet expired (in the sole judgement of the referee).
  So the originator sends a message to the referee requesting permission to commit.

  Assuming permission/authorization is given by the referee, the requester now possesses a digital signature of the referee indicating that the lift is good and valid.
  It will proceed to transmit this information clockwise through the lift chain, starting with node B.
  Node B will forward the signature to C, and so forth until all the nodes in the circuit have received the signature.
  Each node can make the lift chits binding by affixing this signature to the chit record.

![seq-lift-conf](uml/seq-lift-conf.svg)

#### Referee Queries
  Assuming all the nodes stayed connected and responded correctly through the lift sequences above, everyone now has exchanged their excess credits and collected other, more wanted ones in their place.
  But if part of the network had a problem part-way through the lift, some nodes might be left in an indeterminate state.
  They are committed to the lift, but they don't have the required signature to complete so they really don't know for sure if the lift should go through or not.

  Participating nodes can consult their local clock and get a pretty good idea of when the lift should have timed out.
  If this time is exceeded, they can reach out to the referee node to ask the status of the lift.
  The referee will:
  - respond with a "timed out" message; or
  - provide the authorization signature.

![seq-lift-ref](uml/seq-lift-ref.svg)

As a further optimization, it will provide a greater of load distribution if nodes suspecting a timeout will first try reaching out to the lift originator to validate a lift.
The originator shall respond similarly to any query with one of the following answers:
- The lift is good; here's the referee's signature;
- The lift has timed out, here's a signed timeout message from the referee;
- I don't yet have an answer for this lift

As long as connectivity can be maintained with their upstream neighbor, the originator, or the referee, each node should be able to successfully complete the lift.
If none of these can be reached, the lift commit will block indefinitely until connectivity can be restored.

It [has been shown](../test/analysis/dsr/phase-1/results.md) that without a referee, the protocol suffers from potential safety and/or liveness issues.
So it is important that sites maintain a list of trustworthy referees and their public keys.
To support this function, a site willing to serve as referee must also support the following auxiliary protocol:

![seq-ref-aux](uml/seq-ref-aux.svg)

In general practice, it is expected that each host site will execute a tally with referee sites they expect to honor.
Such tallies can contain contractual language expressing the referee's willingness to conduct its function with fidelity and good faith.
This also supports the possibility of assessing fees in exchange for referee services where applicable.

The Term of Service describes how long the referee commits to perform lifts.
This will allow a service provider to discontinue service without breaking trust or losing reputation.

#### Lift States
Now we can derive the following state diagram to describe the lift protocol from the perspective of a single site:

[![state-lift](uml/state-lift.svg)](uml/state-lift.svg)

The referee lift state diagram is as follows:

[![state-ref](uml/state-ref.svg)](uml/state-ref.svg)

### Consensus Protocol
This is a sub-protocol by which the peers at each end of a common tally agree upon which order chits are entered onto their copies of the tally.
Chit order is not particularly important from a theoretical standpoint.
But in an actual implementation, it is very helpful.

Each chit contains a hash of its other contents.
This hash is useful for detecting if anything in the chit has changed (something we don't want to happen).

In addition, each chit contains a copy of the hash for the chit preceeding it on the tally.
In this way, the hash of the latest chit can be compared with the same point in the chain on the other end of the tally.
If the hashes are the same, we can rest assured that the stock and foil contain exactly the same chit information, at least up to that point.
This is much more efficient than trying to compare every chit on the tally individually each time.

Chits can originate from either end of the tally.
For example, either party can unilaterally sign a chit that sends value to the other party.

![use-cons](uml/use-cons.svg)

In the case of lift chits, validating signatures will normally propagate around the lift circuit in the clockwise (downstream) direction.
That means the foil holder on any given tally will get the signature before the stock holder.
As they attempt to reach consensus on chit order, the signature will naturally get shared.

This diagram shows the sequence of events for the two basic use cases:

![seq-cons](uml/seq-cons.svg)

The consensus algorithm is pretty simple.
Essentially, the foil is always right about how to order the chits.
It is the job of the stock to conform to that order.

Both stock and foil have the duty to recognize, accept and store a duly signed and valid chit.

The goal of the consenus protocol is then to:
- get all valid chits linked into a hash-chained list; and
- verify that the stock and foil both have an identical list of valid chits.

The consensus protocol is centered around chits.
But it is really the tally (its two halves) that are (or are not) fully consensed at any given time.

Now we can derive the following state diagram to describe the tally/chit consensus protocol from the perspective of a single site.
First, the states associated with the foil:

[![state-cons](uml/state-conf.svg)](uml/state-conf.svg)

And now, the states associated with the stock:

[![state-cons](uml/state-cons.svg)](uml/state-cons.svg)

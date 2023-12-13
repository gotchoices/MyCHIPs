<div style="display: flex; justify-content: space-between;">
  <a href="README.md#contents">Back to Index</a>
  <a href="learn-network.md">Next</a>
</div>

### Credit Lifts Explained
For a higher level overview of the lift algorithm, consider first reading [this article](http://gotchoices.org/mychips/acdc.html).

The following figure considers four trading entities consisting of two people and two companies.
The arrows indicate the normal flow of payments, or credit promises.

![A Simple Lift](figures/Lifts-1.jpg "Visualizing a Lift With Four Participants")

Presumably, products and services are flowing in the opposite direction.
For example, person B works for company A and shops at company C.
Person D works for company C and shops at company A.

Obviously, entities do not always have to alternate between companies and people in this way.
But this simplified diagram allows us to define an *upstream* partner as one you sell product or servies to.
A downstream partner is someone you buy things from.
It doesn't really matter if your partners are people or companies.

As products/services are delivered, payment is made in the form of private credit, or an IOU.
As this is an accounting function, it has a *dual-entry* nature (debit and credit).
A credit (negative, liability) is entered by the entity (A) making payment.
A debit (positive, asset) is entered for the entity (B) receiving payment.
If the signs of these transaction don't make sense to you, consider reading [this article](http://gotchoices.org/book/account.html).

Keep in mind, these debits and credits themselves do not actually *flow* all the way around the circle.
For example, if A gives an IOU to B, that *specific* IOU does not flow along to C.
Since MyCHIPs is a *private credit* model, credits are not transferrable.
A credit agreement is just between you and your direct partner--not some other entity you may not know or trust.

One important goal, however, is to make these credits useful anywhere in the system.
Because they are private and non-transferrable, they are not *fungible* like traditional money.
But the lift algorithm will allow us to accomplish something arguably even better: transmutability.

This means you can *make* payment using the type of credits you *have* and your 
seller will *receive* payment in the type of credits it *wants.*

After a sufficient volume of selling, each entity will have accumulated some amount of asset value in IOU's from the entity just upstream.
As one might imagine, this can only go on so long.
If B gets too many IOU's from A, eventually it won't want any more.
It has reached its maximum "trust level," or "credit limit."

What B really needs are some IOUs from C where B buys things.
The lift function will allow B to give up some of its A credits in exchange for some C credits, just what is wanted to complete needed purchases.

In order to accomplish this, we need to find a complete *circuit.*
This is where entity D will be helpful.
If we can, all at once, send a fixed number of credits around the circuit in the upstream direction (against the direction of the arrows), everyone's excessive buildup of IOU's can be relieved a little bit without costing anyone anything.
This is called *credit clearing.*

Everyone around the circuit will benefit from this transaction because they will all give up credits they don't need in exchange for credits they do need.
But we will need a way to do this so no one gets hurt--particularly if someone in the circle tries to cheat.

One way to accomplish this is to use a transactional database.
We could group the four separate credit exchanges belonging to a single lift and
make them part of an
[atomic database transaction](https://en.wikipedia.org/wiki/Atomicity_%28database_systems%29).

This means the database will attempt all four transfers, but if any one of them fails, the other three will also be canceled.
The lift will either work in its entirety, or it will not work at all.
The goal is to make sure no one is left giving away credits but not getting others of equal value in return.

Now some bad news:  In order to do this, we would need to have all our entities in a single database.
That means our system would be very centralized and unscalable--just what we are trying to avoid with MyCHIPs.

It would be nice to have an algorithm that could achieve an atomic result even when all four of our users have their data in different databases on different 
computers distributed around the Internet.  

And now, more bad news:
That [isn't possible.](https://en.wikipedia.org/wiki/Two_Generals%27_Problem)

This is actually a pretty old problem.
It is hard enough to get a group of updates to operate as a single transaction inside a single database.
But to do this over unreliable links, or with other peers you may not know or be able to fully trust, it probably just can't be done.

To get over this otherwise insurmountable hurdle, MyCHIPs makes a simple compromise:
instead of making sure *no one* gets hurt during a lift, we will instead, be satisfied if we can make sure no *responsible* party gets hurt.

We will set up our transaction in some basic phases.

In the first phase, we will discover circuits, or routes through the network that are capable of supporting the lift.

In the next phase, we will initiate a proposed lift around that circuit.
Each peer who is willing to participate on the suggested terms will give a conditional commitment.
This commitment is structured as a digital contract which, when properly signed, becomes a binding CHIP credit.
In other words, it is money (value) to the recipient and debt to the issuer.
It just lacks a certain digital signature to become valid.

In the final phase, we will attempt to fully ratify each conditional credit to make it valid and binding.
This is where the Two Generals dilemma would deny us success if we were depending on a fully transactional commit.
It would be possible for someone to conditionally commit in the first phase, but then fail to cooperate in the final commitment phase.

But because everyone already posesses conditional credits lacking only the proper digital signature, all we really need is a way to get that signature out to everyone and they will have their promised money.
Any *deadbeat* who drops off the network between these two phases will simply miss out.
It has already given conditional approval in the previous phase, so its immediate peer can prove it is part of the lift and owes the value.
It is the deadbeat itself who lacks the signature needed to be made whole.

This is not to say that everyone is happy about the deadbeat.
Its upstream partner may have a potential collection problem (at least if the balance runs into negative numbers).
But that is a risk it signed up for when initiating a tally with the deadbeat.
Hopefully there is collateral or some other way to collect the debt.

The deadbeat's partner on the downstream side has the opposite effect.
It received the credits wanted in the lift, but doesn't have to give anything up until the deadbeat gets back on line and completes the transaction.

The deadbeat has the further problem that it may have *burned its bridge* to the network of trust.
The two entities who know and trust it, now know it is either up to no good or at least, unreliable.
No further traffic can be performed by this entity--at least through the peers it has just disappointed.

The technical challenge in implementing the distributed lift function is as follows:
During the conditional commit phase, the peers need to negotiate a chain of commitments
around the circuit which the lift signer can fully validate, proving that
each pair of peers along the route has agreed to the transaction, pending the signature itself.
Then, the signer can form this final signature and send it back around the loop.
If it sends it in both directions (up and down stream), everyone involved in the process, except a single deadbeat can get the final signature they need.  

If there are two deadbeats in a single lift, it is possible for them to deprive everyone between them of the final signing key.
This could conceivably be orchestrated between two corrupt nodes on the network, working together and using a modified version of the server.

A strategy to combat the "two-deadbeat" dilemma is to include as part of the earlier phase, public contact information about the lift signer.
If parties don't receive the final signature through the linear pathway of the lift, the transaction would time out.
Then, the stranted parties could reach out directly to the lift signer to obtain the needed signature.

### Linear Lifts
The lift algorithm above is described for a complete circuit and is useful for clearing accumulated credits.

It is also possible to perform a *linear lift* which begins and ends with different nodes.

![A Linear Lift](figures/Lifts-2.jpg "A Lift to Transmit Value")

In this example, entity D meets entity A through some trading opportunity (like an online auction site).
Due to the reputation of the site, D trusts A enough to believe it will actually ship the product or services so now D wants to pay A.

However, they don't know each other well enough to establish a tally directly between them.
Perhaps A doesn't trust an IOU from D or maybe this is a one-time transaction and they don't otherwise want to maintain an ongoing relationship.

In this case, it is not necessary to discover a complete circuit of credits.
We just need a pathway of tallies connecting D to A.

Node D will lose some credits on its tally with C.
Nodes B and C will break even, but they will get some credits cleared so there is an incentive to participate.
Node A will gain some credits on its tally with B.

We can see that this linear case is almost identical to the circular example previously given.
The primary difference is there is no tally between A and D.

MyCHIPs allows a payor to pay with what it *has but doesn't need* while the recipient receives
what it *needs but doesn't yet have.*

### Credit Lift Algorithm

In order to perform lifts, nodes must have some idea of where to send credits so they will arrive at their intended destination.
If there could be a single, giant database of all the tallies in the world, this might not be such a difficult task.

But MyCHIPs is purposely designed as a <a href="https://blockchainengineer.com/centralized-vs-decentralized-vs-distributed-network/">fully distributed</a> system.
The intent is, no single database will contain knowledge about the whole network.
Rather, databases should only contain detailed information about the *local* entities they host and other *foreign* entities their local users are directly connected to by tallies.

To accomplish this, each node will have to cooperate with its neighbors to discover theoretical routes that may exist through the network.
For the purposes of regular (circular) lifts, the goal is to find external routes:
- from known, upstream (owe us value) foreign entities,
- to known, downstream (we owe value to) foreign entities.

Discovering such external pathways, a site should be able to combine them with known, internal segments of entities to form a complete lift circuit.

<p align="center"><img src="figures/Lifts-3.jpg" width="400" title="A distributed lift"></p>

For linear (payment) lifts, the process is similar.
The goal is to find external pathways:
- from a known, upstream foreign entity,
- to a particular, identified foreign entity,
- who may also have provided *hints* about one or more well-known entities it has a direct downstream connection to.

We use the terminology *upstream* to denote a peer who owes us excess value.
This is most often associated with a tally of which we hold the stock but it is also possible to accumulate excess CHIPs on a tally foil.
An employer or customer is a good example of a partner you would normally find upstream from you.

We use the terminology *downstream* to denote a peer we might owe value to.
Alternately, it could be someone who owes us less than we want them to.
This is often associated with a tally of which we hold the foil but it is also possible to have fewer CHIP credits than we want on a tally stock.
A merchant or supplier is a good example of a partner you would normally find downstream of you.

<p align="center"><img src="figures/Lifts-6.jpg" width="500" title="Sites contain multiple users"></p>

This figure shows a convenient way to visualize a lift pathway in a real implementation.
A site database may contain multiple entities who are connected in a short, linear segment.
Some of these are local, meaning their accounts are hosted by the site.
For example, site B hosts users B1, B2 and B3.
But a lift will probably be moving upstream through them, so we would describe the segment in the direction of the lift as [B3, B2, B1].

Hopefully, each chain will begin and end with two or more foreign users (hosted by some other site).
Otherwise, a distributed lift through the segment will not be possible.
For example, the chain [B3, B2, B1] is also connected to an upstream foreign peer A3 at its top end
and a downstream foreign peer C1 at its bottom.

Site B knows about a complete segment [A3, B1, B2, B3, C1].
But that is where site B's direct knowledge about the network ends.
It will be reliant on site A, site B, and probably a bunch of other sites to execute a complete distributed lift.

Sites typically will know nothing about the internal ID of users hosted on other sites.
Information about the foreign peers at the end of a segment is derived from the partner certificate stored in the asociated tally.
A CHIP address (cid:agent) is found there, but no local ID that can be used for linking segments.

So a lift segment can be defined as:
- One or more local entities connected in a linear chain; and
- A foreign entity at the top of the chain; and
- A foreign entity at the bottom of the chain.

The *lift capacity* along a segment is computed by comparing the ability/desire of each entity in the chain to perform a lift.
Individual entities define [trading variables](learn-tally.md#trading-variables) that control how many credits they would like to maintain on any given tally.

<p align="center"><img src="figures/Lifts-5.jpg" width="400" title="Computing lift capacity"></p>

The lift algorithm compares the actual tally balance to the *desired* balance to arrive at a lift capacity.
Using this [interactive figure](https://cdn.jsdelivr.net/gh/gotchoices/MyCHIPs/doc/figures/lifts.svg)
you can visualize how trading parameters determine lift capacity.

### Lift Route Calculation
The original MyCHIPs protocol involved caching lift routes so they would not need to be discovered anew each time a lift is contemplated.
As of Version 1.4, thisstrategy is abandoned and routes will be queried for as needed.

Routes will contain an internal data structure that is anonymized so it does not disclose confidential information to other nodes that may posess it.
But the information can be understood by each node along the way so as to remember how to process the lift if/when it is called for.

### Lift Costing
Refer to the included [costing spreadsheet](Costing.ods).
This shows how costs are propagated through a chain of tallies.
At each node, the cost may be 0, a positive percentage, or a negative percentage.
A negative cost implies the node will be paying to participate in the lift.
A positive cost implies the node will be charging others to use its channel for the lift.

At each node, the total accumulated cost is the current nodes percentage,
applied to the remaining basis resulting from application of the cost of all
prior nodes:
```
  NewRate = PriorRate + MyRate * (1 - PriorRate)
```
Trading costs/rewards are computed according to the tally [trading variables](learn-tally.md#trading-variables).
Each user adjusts these values to indicate his appetite for collecting the 
credits associated with that tally.

Note that no user may apply a charge for a lift that would reduce the debt it owes to its partner back to zero.
That debt is an IOU and must be honored without further expense.
However, users may charge (reward) for lifts that put them in debt beyond the target amount specified in their trading variables.
They may also charge (clutch) for lifts that would increase their indebtedness to their partner.

This figure shows how/where the margin and clutch values come into play.
<p align="center"><img src="uml/trade-seq.svg" title="Visualizing Lifts and Drops"></p>

### Lading Capacity
Lading describes the capacity of a route to handle a lift of a given size.

As a route is computed, we will aggregate these values from one site to the 
next to determine the size of a possible lift distributed across multiple sites:

-  **min**:	The least amount some along the route is willing to lift for free.
-  **max**:	The most one can expect to lift along this route, possibly at a cost.
-  **margin**:	Combined fees (usually zero) for any lift, less than min.
-  **reward**:	An additional fee for lift amounts over min, up to max.

### Lift State Analysis
In order to understand how to maintain state for routes and lifts, let's first consider some possible scenarios.
A lift may be initiated in several different ways:

- **Local Clearing**: The local system automatically detects a circuit which can be lifted to mutually clear credits.
    The transaction can be handled locally requiring no interaction from other sites.
    Chits can be signed by local agent authorities.

- **Local Linear**: Similar to the Local Clearing case except the lift is used to make a payment from one user to another on the same system.
    The lift itself must be signed and authorized by the payor party but chits themselves can be signed by local agents.

- **Distributed Clearing**: The system detects a local segment which is 
    in need of a lift (has a mutually correlated credit imbalance).
    It initiates a process to discover/utilize an external pathway from a the segment's upstream foreign node to its downstream foreign node.

- **Distributed Linear**: One of our local users initiates a transmission of value to 
    a peer it is not directly connected to and who is not hosted by the local system.
    It initiates a process to discover/utilize an external pathway from the local user, through a connected upstream node and to the target recipient.

- **Relay**: The system receives a lift request from downstream, bound for a peer we 
    do not host or otherwise have a direct connection to.
    Hopefully we are able to relay the request and then participate in the lift when it finds a completed pathway.
    It makes no difference whether the lift is circular or linear.

- **Target**: We receive a request from downstream for a circular or linear lift.
    The target of the lift is a user we host.
    Linear and circular lifts are treated very similarly with the exception that the circular lift contains one more tally, connected back to the originator.

### Lift States
It was originally thought that a lift could become an extension of the chit state.
But from a relational viewpoint, a lift is really a *set of chits*, all linked by a single uuid.
To further complicate things, a single lift might involve multiple segments of tallies on a single system.
We really need a separate state record, per segment, to keep track of all the tallies/chits that are part of the lift.

In a distributed lift, each system will identify one or more local users arrayed in a linear segment with one foreign peer at each end of the chain.
When a single database commits its portion of a lift, it should atomically commit all the tallies along the segment.

A lift consists of several phases:
- **Phase 1**: Seek/discover a routing pathway for the lift and its desired amount
- **Phase 2**: Send a conditional lift proposal around the circuit, upstream
- **Phase 3**: Resolve validation/cancellation (typically downstream) through the circuit
- **Cleanup**: Respond as needed to requests for validation signatures

To help track this, a lift record will be marked by one of the following types:
- **in**: The lift is entirely contained on the local system.
- **org**: A distributed lift that was originated on this system.
- **rel**: A distributed lift which originated on some other system.

Lift records also have a state which is one of the following:
- **route**: The user or system is considering a lift.
	Detecting this state, the agent should initiate route discovery for the intended lift.

- **init**: The user or system has marked the lift to begin.
	This should trigger action to either complete the lift locally or to 
	propagate the lift to the appropriate upstream partner.

- **seek**: The lift, originated on this system, has been propagated to externally and we are waiting for it to find its destination.

- **found**: The target of a distributed lift was found on the local system.
	Will notify the agent of the intended terminus user.

- **term**: The terminus agent has been notified of the lift.

- **pend**: The lift is being ratified but we don't have a validating signature yet.

- **good**: The lift has the required ratifying signature(s).

- **void**: The lift has been marked as timed out with the required, voiding signature(s).
  
### The Lift Record
Linear, or payment lifts must be digitally signed by the payor.
This authorizes the agent to perform the lift on the user's behalf.
The record to be signed consists of the following properties:
```
lift: {
  uuid: "9e61301c-86aa-5835-abcd-25adf13eaf3c",
  find: {
    cid: <optional CHIP ID of payment recipient>
    agent: <recipient Agent address>,
    host: <optional agent host address>,
    port: <optional agent host port>
  }.
  date: <Lift initiation date/time>,
  units: <value of lift>,
  memo: <Human-readable text message from payor>,
  ref: <JSON invoice or transaction reference>,
}
```
All lift records (and their associated chits) are signed by agents as they are passed along the lift route.
The agent signs a record consisting of these properties:
```
relay: {
  uuid: "9e61301c-86aa-5835-abcd-25adf13eaf3c",
  date: <Lift initiation date/time>,
  life: <How manys seconds before the lift expires>,
  play: <Path, routing, margin, payment information, encoded for agents' eyes only>,
}
```
Each of these records can be presented along with a further property *sign* that contains one or more signatures of authorized users or agents.

The *play* property contains routing information derived from the route discovery phase.
This information may be encrypted in such a way that it can only be interpreted by agents along the way.
It will also contain encrypted information readable only by the agent at the end of the lift, such as the payment details from the payor:

```
payment: {
  units: <value of payment>,
  memo: <Human-readable text message from payor>,
  ref: <JSON invoice or transaction reference>,
}
```

<div style="display: flex; justify-content: space-between;">
  <a href="README.md#contents">Back to Index</a>
  <a href="learn-network.md">Next</a>
</div>

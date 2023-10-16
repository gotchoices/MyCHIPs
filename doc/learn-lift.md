<div style="display: flex; justify-content: space-between;">
  <a href="README.md#contents">Back to Index</a>
  <a href="learn-network.md">Next</a>
</div>

### Credit Lifts Explained
The first two levels of the peer-to-peer protocol deal primarily with transactions moving value between two partners who are directly connected by a tally.
Transactions of this kind are quite limited.

Certainly, one party can pledge value to another.
But here is no obvious way to resolve such pledges (i.e. get paid) other than hoping for some later return of compensatory product, services or alternative money.
MyCHIPs uses a technique called a “credit lift” to 
allows parties to transmit surplus credits (pledges) they hold, back through the network, and have them reappear as credits on other tallies where they can be spent on something you actually need or want.

Think of the [lift algorithm](http://gotchoices.org/mychips/acdc.html) as a way to “pay your bills” without the need for traditional money.
It allows you to trade what you *have but don't need*, for what you *need but don't have*.
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
In fact, a single MyCHIP site with lots of users can do these kinds of "local lifts" where opportunities exist among their own user base.

But MyCHIPs is purposely designed as a <a href="https://blockchainengineer.com/centralized-vs-decentralized-vs-distributed-network/">fully distributed</a> system.
The intent is, no single database will contain knowledge of the whole network.
Ideally, databases will only contain detailed information about the *local* entities they host and other *foreign* entities their local users are directly connected to by tallies.
Even then, information about foreign entities will be kept as limited as possible.

To accomplish this, each database can contain query for theoretical routes that may exist somewhere in the outside network.
For the purposes of regular (circular) lifts, the goal is to find external routes:
- from known, up-stream (owe us value) foreign entities,
- to known, down-stream (we owe value to) foreign entities.

Discovering such external pathways, a site should be able to combine them with known, internal segments of entities to form a complete lift circuit.

<p align="center"><img src="figures/Lifts-3.jpg" width="400" title="A distributed lift"></p>

For linear (payment) lifts, the process is similar.
The goal is to find external pathways:
- from a known, up-stream foreign entity,
- to a particular, identified foreign entity,
- who may also have provided *hints* about one or more well-known entities it has a direct down-stream connection to.

We use the terminology *up-stream* to denote a peer who owes us excess value.
This is most often associated with a tally of which we hold the stock but it is also possible to accumulate excess CHIPs on a tally foil.
An employer or customer is a good example of a partner you would normally find up-stream from you.

We use the terminology *down-stream* to denote a peer we might owe value to.
Alternately, it could be someone who owes us less than we want them to.
This is often associated with a tally of which we hold the foil but it is also possible to have fewer CHIP credits than we want on a tally stock.
A merchant or supplier is a good example of a partner you would normally find down-stream of you.

<p align="center"><img src="figures/Lifts-6.jpg" width="500" title="Sites contain multiple users"></p>

This figure shows a convenient way to visualize a lift pathway in a real implementation.
A site database will contain multiple entities who are connected in a short, linear segment.
Some of these are local, meaning their accounts are hosted by the site.
For example, site B hosts users B1, B2 and B3.
But a lift will probably be moving upstream through them, so we would describe the segment in the direction of the lift as [B3, B2, B1].

Hopefully, each chain will begin and end with two or more foreign users (hosted by some other site).
Otherwise, a distributed lift through the segment will not be possible.
For example, the chain [B3, B2, B1] is also connected to an up-stream foreign peer A3 at its top end
and a down-stream foreign peer C1 at its bottom.

Site B knows about a complete segment [A3, B1, B2, B3, C1].
But that is where site B's direct knowledge about the network ends.
It will be reliant on site A, site B, and probably a bunch of other sites to execute a complete distributed lift.

Note: As of Feb 2022, local path segments handle foreign peers differently.
Older versions maintained an explicit entity ID (in the peer table) for remote peers and those ID's formed the top and bottom endpoints of segments.
More recently, segments are only connected in the middle by local user ID's and the ends are characterized by no ID at all (a NULL).
So the internal representation of the B segment would be: [NULL, B3, B2, B1, NULL].

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

As of February, 2022 lifts have been generalized to include transactions that move upstream *or downstream* (technically a *drop*).
Previously, segments were linked by joining tallies together stock-to-foil.
So one could only consider a lift or a drop across the complete segment.

Now tallies are linked together according to their capacity to flow (lift) value in either the stock-to-foil or foil-to-stock direction.
In fact, a single tally might simultaneously be a candidate for a lift and a drop, as a member of different segments.
This will allow much more flexibility for users in controlling their accumulated balances.

So as the terms *upstream* and *downstream* are used in relation to a lift,
*upstream* simply means in the direction we want the lift value to flow and *downstream* means the opposite.

### For More Background
The reader may derive more background on the credit lift may also read this
[now obsolete section](old-lift.md) written prior to the 1.0 protocol.

<div style="display: flex; justify-content: space-between;">
  <a href="README.md#contents">Back to Index</a>
  <a href="learn-network.md">Next</a>
</div>

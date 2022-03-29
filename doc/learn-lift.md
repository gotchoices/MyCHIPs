## Lift Logic

Note:  
This section was originally written in February 2020, prior ot the development 
of the [1.0 protocol](learn-protocol.md).  The information here is helpful and 
informative, but may not be entirely consistent with the newer protocol.

For a higher level understanding of the lift algorithm, consider first reading
[this article](http://gotchoices.org/mychips/acdc.html).

As we discuss the alorithm, we will refer to the following figure:

![A Simple Lift](figures/Lifts-1.jpg "Visualizing a Lift With Four Participants")

This example considers four trading entities.  In this example, there are two people
and two companies.  The arrows indicate the normal flow of credits, or credit
promises (think of payments).  So presumably, products and services are flowing 
in the opposite direction.

For example, person B works for company A and shops at company C.  Person D
works for company C and shops at company A.

Entities do not always have to alternate between companies and people in this 
way.  But generally, you are selling something (product, services, or labor) to 
the entities upstream from you and you are buying something (product, services
or labor) from the entites downstream.  This can really include any combination
of people and companies.

As products and services are delivered, payment is exchanged in the form of
private credit, or an IOU.  As this is an accounting function, it has a dual
entry nature (debit and credit).  A credit (negative, liability) is entered for 
the entity (A) making payment.  And a debit (positive, asset) is entered for 
the entity (B) receiving payment.

If the signs of the transaction didn't make sense to you, consider reading
[this article](http://gotchoices.org/book/account.html).

Keep in mind, these debits and credits themselves do not actually *flow*
all the way around the circle.  For example, if A gives an IOU to B, that 
*specific* IOU does not flow along to C.  Since MyCHIPs is a *private credit*
model, it means just that.  Your credit is private.  It is just between you 
and the entity you do business with directly--not some other entity you 
might not know or trust.

However, the goal is to make these credits fungible, or in our case, 
*effectively fungible.*  So although we can't literally substitute one entity's 
credits for another, the lift algorithm will allow us to accomplish
something that is arguably even better:

> You can *make* payment using the type of credits you *have* and your 
seller will *receive* payment in the type of credits he *wants.*

After a sufficient volume of selling, each entity will have accumulated some
amount of asset value in IOU's from the entity just upstream.  As you can 
imagine, this can only go on so long.  For example, if B gets too many IOU's 
from A, eventually he won't want any more.  He has reached his maximum "trust 
level," or "credit limit."

What B really needs are some IOUs from C where B buys his stuff.  The lift 
function will allow B to give up some of his A credits in exchange for some C 
credits, just as he needs to complete his purchases.

But in order to accomplish this, we need to find a complete *circuit.*  This
is where entity D comes in so handy.  If we can, all at once, send a fixed 
number of credits around the circuit in the upstream direction (against the 
direction of the arrows), everyone's excessive buildup of IOU's can be 
relieved a little bit without costing anyone anything.

Everyone around the circuit will benefit from this transaction because they
will all give up credits they don't need in exchange for credits they do need.
However, we will need a way to do this so no one gets hurt--particularly
if someone in the circle tries to cheat.

One way to accomplish this is to use a transactional database model.  The idea
is to queue up all four credit exchanges belonging to a single lift and
make them part of an [atomic database transaction](https://en.wikipedia.org/wiki/Atomicity_(database_systems)).
This means the database will attempt all four transfers, but if any one of 
them fails, the other three will be canceled.
So the lift will either work in its entirety, or it will not work at all.
The main goal is to make sure we don't perform only part of the lift, 
leaving someone out so they end up giving credits away, but not getting the 
ones they expect in return.

Now the bad news:  In order to do this, we would need to have all our entities 
in a single database.  That means our system would be very centralized and 
unscalable--just what we are trying to avoid with MyCHIPs.

Centralization is prone to manipulation and corruption.
It is also not scalable--the critical feature we need to surpass what 
other alternative systems (like blockchain) have been unable to achieve.

It would be nice to have an algorithm that can achieve an atomic result even 
when all four of our users have their data in different databases on different 
computers distributed around the Internet.  

And now, some more bad news:
That [isn't possible.](https://en.wikipedia.org/wiki/Two_Generals%27_Problem)

It turns out this is a pretty old problem.  It is hard enough to get a group
of updates to operate as a single transaction inside a single database.  But
when you are trying to do this over unreliable links, or with other peers you
may not know or be able to fully trust, it probably can't be done.

So to get over this otherwise insurmountable hurdle, we are going to make a
simple compromise:  Instead of making sure no one gets hurt during a lift, we
will instead, be satisfied if we can make sure no *responsible* party gets hurt.

To do so, we will set up our transaction in several basic phases:

In the first phase, we will discover circuits, or routes in the network which 
might be capable of supporting a lift.

In the next phase, we will initiate a proposed lift around that circuit.
Each peer who is willing to participate on the suggested terms will give a 
conditional commitment.  This commitment is structured as a digital contract
which, when properly signed, becomes a binding CHIP credit.  In other words,
it is money (value) to the recipient and debt to the issuer.  It just needs 
a certain digital signature to become valid.

In the final phase, we want to lock down each conditional credit and make it
real, valid and binding.  This is where the two generals dilemma would hurt us
if we were dependent on a fully transactional commit.  It would be possible for
someone to conditionally commit in the first phase, but then fail to cooperate
in the final commitment phase.

However, because everyone already posesses conditional credits lacking only
the proper digital signature, all we really need is a way to get that signature
out to everyone and they will have their promised money.
Any *deadbeat* who drops off the network between these two phases will simply miss out.
He has already given
his conditional approval in the previous phase, so his immediate peer can prove
he is part of the lift and owes the value.  It is only the deadbeat himself who
is lacking the final credits he needs to be made whole.

This is not to say, everyone is happy about the deadbeat.  His upstream partner
may have a potential collection problem (at least if his balance runs into 
negative numbers).  But that is a risk he signed up for when initiating a tally
with the deadbeat.  Hopefully he has collateral or some other way to collect if
credit has been extended in the first place.

The deadbeat's partner on the downstream side has the opposite effect.  He got
the credits he wanted in the lift, but doesn't have to give anything up until
the deadbeat gets back online and completes the transaction.

The deadbeat has the further problem that he may have burned his bridges to the 
network of trust.  The two entities who know and trust him, now know he is either
up to no good or at least, unreliable.  No further traffic can be performed by 
this entity--at least through the peers he has just disappointed.

So the challenge in implementing the distributed lift function is this:  During
the conditional commit phase, the peers need to negotiate a chain of commitments
around the circuit which the lift originator can fully validate, proving that
each pair of peers along the route has agreed to the transaction, pending the
signature of the initiator himself.  Then, the initiator can form this final
signature and send it back around the loop.  If he sends it in both directions
(up and down stream), everyone involved in the process, except a single 
deadbeat can get the final signature they need.  

If there are two deadbeats in a single lift, it is possible for them to
deprive everyone between them of the final signing key.  This could conceivably 
be orchestrated between two corrupt nodes on the network, working together and 
using a modified version of the server.

However, they can only do damage if the lift will run them into credit 
territory (i.e. a negative balance) with the party they are attemping to harm.  
That credit relationship won't last for long, and is a risk the issuer of 
credit knowingly signed up for.

One alternate strategy to combat the "two-deadbeat" dilemma is: Publish, as
part of the earlier phase, an endpoint controlled by the initiator of the lift.
This is the same party who will be issuing the final ratifying signature for
the lift.  If parties don't receive the final signature through the linear
pathway of the lift, the transaction would time out.  Then, the stranted 
parties could reach out directly to the lift initiator to obtain the final
authorizing signature (or be told that it has been rolled back and can be
ignored).

### Linear Lifts
The lift algorithm described above is performed in a complete circle.  Its
function is to balance credit surpluses and deficits around a full circuit of 
trading entities.  So the assumption is, a bunch of people have already been 
trading using existing private credit relationships, and they want to 
participate in a lift to relieve built up credits so they can keep going.

But there is another kind of lift possible and it travels in a straight line.  

![A Linear Lift](figures/Lifts-2.jpg "A Lift to Transmit Value")

In this example, entity D meets entity A through some trading opportunity (like
an online auction site, for example).  Due to the reputation of the site, D
trusts A enough to believe he will actually ship the product or services so now
D wants to pay A.

However, they don't know each other well enough to establish a trading tally
directly between them.  They just want to get this one transaction done, and 
that will likely be the end of it.

In this case, we don't need a complete circuit of credits.  We just need
"nearly a circuit" or a circuit, with the exclusion of a direct credit link 
between A and D.

In this case, no credit transaction will flow between A and D.  We have the
product or services to account for that.  We will just need to negotiate one
or more lifts which add up exactly to the value meant to be transmitted from
D to A.  If we can find enough cooperating parties willing to do so in a path
that starts with D and ends with A, we can complete the transaction.

In nearly every other way, this is identical to a circular lift.  But the
special case does need to be accommodated.  In fact, it may well turn out to be
the more prevalent form of lift.

### Lift Algorithm
The following sections are no longer fully accurate as of the introduction of the
of the [1.0 protocol](learn-protocol.md#lift-protocol).

If lifts were to be discovered and executed in real time, the process would be
something like the following:

- Query foils (downstream tallies) that are below target levels
  - A negative number is credit that needs to be paid at least back to zero.
  - Some foil tallies will have higher (positive) targets to accumulate a debit 
    balance so it can be spent later.
- Identify the target foil to lift (we will call this vendor peer V)
- Compare the amount desired to lift for the target foil to available 
  accumulations on active stocks.
- Pick a stock (upstream tally) to target for the lift.
- Query the upstream peer for that stock (customer peer C) to see if he knows 
  how to reach V upstream somewhere.
- If our query goes unanswered, or answered negatively, try to select another
  eligible stock and repeat the query with that upstream peer.
- If/when we get an affirmative answer back (via V) from an upstream peer, 
  proceed to initiate a lift.

- The original search query has a UUID that may have been cached upstream.
- Promote the status to "request", insert the actual amount, and repeat the 
  query.
- This request should propagate all the way around the circle and come back to
  us via peer V.

### Lift Calculation
In reality, it wouldn't be very efficient to recalculate every lift pathway
from scratch.  Rather, we will populate a database with information about our
own local users and the foreign users they share tallies with that will help 
us figure out pathways in advance that are likely to succeed.  Successful 
pathways can be used over and over again.

Our local database already contains information about how our local users are
related to each other.  If they share a tally, we know that.  And we know who
holds the stock and who holds the foil.

In addition, we have data about certain foreign peers.  Although we don't host 
these users, we still know about them because they share tallies with users in
our system.

What we would like to collect is data about how these foreign users might be
linked to each other in the outside world.  But those details may be private 
and not something others want to share with the world.  So what we can settle
for is just the knowledge that a pathway exists, even if we don't know all the
parties along that pathway.

For example, let us consider the following set of connected users:

![A Distributed Lift](figures/Lifts-3.jpg "A Lift That Occurs Across Multiple Databases")

We certainly know about our own users A, and B.  We also know some things about
users C and D.  But we don't really know who C and D are connected to in the
outside world, or if there is a lift pathway from D to C.

If C and D are both hosted by another single database, it would be pretty easy
to just ask: "Hey, are C and D connected?  And is a lift possible going 
through D and eventually getting to C?"  That system could answer the question 
just as easily as we can for our own interconnected users.  And it would not 
really have to give us much information, other than to say that a lift along 
that path is possible.

But what if they are not on the same server?  That is where it gets more
complicated.  Essentially, D's host database would have to note that C is not
its customer, but that it would be useful to be able to find an upstream route
to C, wherever in the world it might be hosted.  And so it could pass the query 
on to those foreign hosts it knows about who are upstream from D.

If one of those systems hosts C, it can answer and D's host can then relay the
information back to A's host.  If not, they can pass the inquiry along for as
long as it takes until either there are no more upstream pathways to query or 
C's host is eventually discovered.

In practice we hope to deliver some hints as well that will make this process
more efficient so hosts don't have to continue sending queryies off in useless 
directions.

### Routes
The route table is used for this purpose.  It is designed to model two 
particular cases:

- **Native**:
  A native route represents a hypothetical link we want to discover that exists 
  outside our own data set *and* completes a partial, local circuit (segment) we 
  already know about.

  As an example, see Peers D and C in the figure.  We would like to find an
  external upstream pathway which leads from D to C.  Since we have peer records
  for both peers, we can represent them by their local ID's in our system.  But
  in order to discover if the proposed pathway is possible, we will have to start
  by querying the system that hosts D.  That leads us to the next case:

- **Relay**:
  On D's system, D is certainly fully known as a user there.  A is also known, but
  in a more limited way--as a foreign peer, not a local user.
  But C may not be known at all.
  So when we ask D's system to help us find the route, it will need a way to store the
  route information even though it has no local record for C.  In this case, it
  will just store the CHIP address and not a local relational link.

  Two further complications:  A relay record represents a query from a downstream
  system.  We may not need to know about this path for the purpose of initiating 
  our own lifts (at least not immediately).  Rather, we hope to get lifts coming 
  from downstream through this channel because it will help our own users.
  Since we don't know where C is 
  ourselves, the only way we can hope to find out is by sending more relay 
  requests to our own upstream peers.  If/when an answer comes back, we will need 
  to remember enough information about our downstream requester so we can tell 
  him properly whether the route has succeeded or failed.

So our complete lift route pathway information system consists of two basic 
data sets:

- The view **tallies_v_paths**: which links all our known tallies together in a
queriable chain of internal pathways; and 
- the table/view **routes/routes_v** which contains both native and relay routes.

Note the "sense of flow" in tallies_v_paths is downstream.  That is, the path
array begins with upstream peers and proceeds downstream.

By convention, the route table has more of an upstream feel to its flow.  That
is, it begins with a foreign peer known to our system, and reaches upward to 
find another external peer we are searching for.

#### Linear Lifts
Finally, we mentioned above that foreign routes may not be locally significant.
But this ignores the significance they may hold for linear lifts.  When
transmitting value along a linear lift path (as opposed to circular), the peer
at the end of the line may very well not be known as a peer or user on our own
system.  Rather, he will be known only by his CHIP ID and host, or possibly
even an anonymized ID known only to the given host.

This kind of query looks very much like a foreign path since it will not 
contain a local ID field.  It could, and may often, be generated by a local
request.  But if foreign queries have previously searched for this user, we
may well have a record in our system telling us just how to find him.  If so,
all the better.  No need to initiate our own query.

Model Requirements (in general terms):
- Native:
  - Route Entity: The local ID of a foreign peer (D) who holds a foil tally with 
  	one of our users (A).
  - Destination Entity: The local ID of a foreign peer (C) who holds a stock 
  	tally with one of our users (B) and can be found at the end of a chain 
  	which starts with the Route Entity (D).
  - Route Key: Some identifier that uniquely identifies this route record which
  	we will pass to our upstream peer.  If the route is found to be good,
  	we expect this key to be returned to us so we know which record to 
  	mark as good.  This might just consist of the Route and Destination
  	CHIP addresses.  It should not consist of our internal ID's for those
  	peers as that might compromise otherwise private information.

- Relay:
  - Route Entity: The local ID of a foreign peer on our system who holds a foil
  	tally with one of our users.  This is not the same as the Route Entity
  	from the downstream system that asked us to relay this route request.
  	Rather this is a peer at the top of a known chain in our system.
  - Destination Peer: This could potentially include a local ID if we happen
  	to know about this peer.  More likely, it is someone we don't have
  	direct knowledge about, so we will have to store it as a CHIP address
  	only.  This is the same peer as the Destination Entity represented in
  	the original native route request that came from somewhere downstream.
  - Route Key: Similar to above, but unique to this record on this system.
  - Return Socket: A connection point (host and port) where we will connect to 
  	return status updates about this route request.
  - Return Key: The Record Key data originally sent from the downstream 
  	requesting system.  We will return this data when reporting on status
  	updates about this route.

### Test Case
Let us assume we have the following set of users hosted on four different systems:
lux0, lux1, lux2, and lux3:

![A Simple Lift](figures/Lifts-4.jpg "Visualizing a Lift With Four Participants")
```
Native:                 (On david_meese's system: lux1)
  Route Entity:         p1004: kathleen_ramsey@lux0             route_ent
  Destination Entity:   p1003: lakisha_villiard@lux2   dest_ent,dest_chid/host
  Route Key:            kathleen_ramsey@lux0 (+lakisha)         (inherent)
  Return Gateway:       p1001: david_meese@lux1                 topu_ent
  Return Key:           p1001: david_meese@lux1                 botu_ent
  Return Socket:        p1001: david_meese@lux1	(inside=native) requ_ent

Relay 1:                (On kathleen_ramsey's system: lux0)
  Route Entity:         p1004: tricia_mayo@lux3                 route_ent
  Destination Peer:     lakisha_villiard@lux2              dest_chid/host
  Route Key:            tricia_mayo@lux3 (+lakisha)             (inherent)
  Return Gateway:       p1002: gena_avila@lux0                  topu_ent
  Return Key:           p1000: kathleen_ramsey@lux0 (+lakisha)  botu_ent
  Return Socket:        p1005: david_meese@lux1:65430           requ_ent

Relay 2:                (On tricia_mayo's system: lux3)
  Route Entity:         p1003: stacey_welch@lux2                route_ent
  Destination Peer:     lakisha_villiard@lux2              dest_chid/host
  Route Key:            stacey_welch@lux2 (+lakisha)
  Return Gateway:       p1000: tricia_mayo@lux3                 topu_ent
  Return Key:           p1000: tricia_mayo@lux3 (+lakisha)      botu_ent
  Return Socket:        p1005: gena_avila@lux0:65430            requ_ent
```

### Lift Costing
Refer to the included [costing spreadsheet](Costing.ods).
This shows how costs are propagated through a chain.
At each node, the cost may be 0, a positive percentage, or a
negative percentage.  A negative cost implies the node will be paying to
participate in the lift.  A positive cost implies the node will be charging
others to use its channel for the lift.

At each node, the total accumulated cost is the current nodes percentage,
applied to the remaining basis resulting from application of the cost of all
prior nodes:
```
  NewRate = PriorRate + MyRate * (1 - PriorRate)
```
Trading costs/rewards are computed according to the tally 
[trading variables](learn-tally.md#trading-variables).
Each user adjusts these values to indicate his appetite for collecting the 
credits associated with that tally.
The lift algorithm is supposed to figure it out from there.

### Lading Capacity
Lading describes the capacity of a chain or a route to handle a lift of a given
size.  See the Tally document for the lower level values computed in views to
determine lading capacity.

In the route table, we aggregate and store these values from one site to the 
next to determine the size of a possible lift distributed across multiple 
sites:

-  **min**:		The least anyone along the chain is willing to lift for free.
-  **max**:		The most you can expect to lift, including at a cost.
-  **reward**:	The foil fee for lift amounts over min, up to max.
-  **margin**:	Combined stock fees (usually zero) for any amount of lift.

### Lift State Analysis
In order to understand how to maintain state for lifts, let's first consider 
some possible scenarios.  A lift can be initiated in several different ways:

- **Local Circular**: Our local system automatically detects a segment which is 
    in need of a lift (has a mutually correlated credit imbalance) and so it 
    initiates a process to discover/utilize an external pathway that can satisfy 
    the lift requirements (relieve the built-up credits).

- **Local Linear**: One of our local users initiates a transmission of value to 
    a peer he is not directly connected to.  This would indicate a potential 
    need to pay someone right then, in real time.

- **Remote Relay**: We receive a lift request from downstream, bound for a peer we 
    do not host or otherwise have a direct connection to.  Hopefully we are
    able to relay the request and then participate in the lift when it finds a
    completed pathway.

- **Remote Linear**: We receive a request from downstream for a linear lift.  This
    will come in from a foreign peer at the base of a segment which connects to
    the intended recipient, a user we host.

- **Remote Circular**: We receive a request from downstream for a circular lift.
    This will come in from a foreign peer at the base of a secment which ends 
    in the foreign user specified as the intended end of the circuit.

These cases really stem from two basic conditions:

- **Local**: Either a user is initiating a linear lift (a payment), or our system
    has detected the need to lift a particular segment, that is hopefully part
    of a larger external circuit.
    
- **Remote**: Some system downstream of us has originated its own local action 
    which has bubbled upstream to arrive at our system.  Either we host the
    intended endpoint of the lift or we will have to pass it on.

More on the five specific modes, starting with simpler cases first:

- **Remote Circular**: This is always a circuit lift.  We can determine our
    system to be the last node in the chain because the destination user is a
    foreign peer who is directly connected to one of our hosted users.  We 
    need to relay the message to the next node--the one that hosts the 
    destination peer, and who originated the lift.  This will complete the 
    circuit.  Then we wait for the final validating signature.  If it doesn't 
    come in time, we must seek it out.
  
- **Remote Relay**: This is pretty similar to Remote Circular.  The main difference
    is, we don't know (or care) if the lift is linear or circular.  We just
    pick an optimal path (if we have one), record a series of conditional 
    chits along the segment, and then pass the lift onto the next node.  Like 
    above, we wait for the validation and/or seek it if necessary.

- **Remote Linear**: Also very similar to Remote Circular in that we have direct
    knowledge of the destination peer (whom we host).  However, there is no
    "next node" to propagate the message to.  We are the end of the line.  We
    will have to make contact with the originator of the lift at the socket
    address provided in the lift.  This is a system we may not necessarily 
    know or trust.  However, if we receive a valid signature matching what
    has been agreed to by our own downstream peer, we can accept the 
    validating signature and then propagate it back downstream.
    
- **Local Linear**: The process should begin by the user searching for a
    connection to a specified peer.  If that peer happens to exist in a local
    segment, upstream of the user, a local lift can be consummated without
    any outside involvement.  But more commonly, the peer will not be found in
    this way, so the request will promote to an upstream pathway query.  State
    can be kept in the paths table with status updates being pushed to the user 
    as they come in.  Eventually, the user should have one or more possible
    paths for the lift, sorted with the most cost-effective option at the top.
    The user can then issue a command to commence payment (a set of conditional
    chits) along a selected pathway.

- **Local Circular**: This is similar to Local Linear except a computer is starting
    the process.  Any time a new chit is recorded, we should run a quick query 
    to see if it has resulted in any imbalances.  This is defined as an actual 
    tally balance that is out of range of the desired balance.  If this is 
    found, we should check the status of our possible upstream pathways.  If 
    they need to be refreshed, we do that now.  If/when the pathways are 
    freshened with hypothetical value limits, we pick the most cost effective 
    pathway and initiate a lift request.

The main complications arise for the Local cases.  If we are a remote node, we
are mostly reactive to the process, indicating our desire and ability to
participate in a particular lift.  When we are handling a local case, we have
more work to do: either make a linear payment, or relieve a credit imbalance.
If our first attempt does not succeed, we will need a way to back out and try a
different option, if one can be found.

Under user control (Local Linear) this should not be too difficult.  Either the
user's payment succeeded or it didn't.  If it didn't, he may have other
(possibly more expensive) options to choose from.

Under autonomous control (Local Circular) the system will need some kind of
state to keep track of what has been attempted already so it can make 
reasonable retries and know when to give up.

### Lift States
It was originally assumed that the lift would be implemented in its own state 
machine, just like the tally, chit, and route states shown in the accompanying 
figures/States.odg file.  Then it was noted that a lift really just consists of 
chits so why not just extend the chit state diagram to implement lifts?

Problem is, a lift is really a set of chits, all linked by a single uuid.  And
all those chits that belong to the same system will need to act in a single, 
unified transaction.  We really need a single state record (per system) to 
represent all the local chits, part of the lift.  It would be difficult to
try to maintain state in multiple chit records all at once.

In a distributed lift, each system will identify one or more local users
arrayed in a linear segment with one foreign peer at each end of the chain.  
For example, see the "Route Test Case" figure referenced previously.  Gena 
Avila and Kathleen Ramsey are the two local users.  Tricia Mayo and Stacey 
Welch are the foreign peers at the two ends of a segment which could possibly 
be found to be part of a larger, external circuit.

When a single database commits its portion of a lift (whether conditional or
final), it should atomically commit all the tallies along the segment.  In this 
example, there is a stock from Tricia to Gena, a stock and foil between Gena 
and Kathleen.  And a single foil from Kathleen to Stacey.  That is four tallies 
in total (on our system) which will receive a lift chit, marked with the UUID 
unique to the particular lift, and eventually signed by the lift initiator.

Conclusion is, we do need a lift table containing a lift record with its own
state.  This record will, at some point in the process, refer to a set of
pending chits, which will commit all-or-none.

It was noted earlier, the lift phases are:
- **Phase 1**: Seek/discover a circuit or path for the lift and its amount
- **Phase 2**: Send a conditional lift proposal around the circuit, upstream
- **Phase 3**: Issue validation/cancellation downstream through the circuit
- **Cleanup**: Respond (indefinitely) to requests for validation of the lift

Valid states for the lift record are as follows:
- **init**: We have identified a lift segment we will now propose to the 
	outside network.  This is a result of the user interacting with his UI 
	to pay someone, or it may be a circular lift initiated automatically by 
	the site.

- **seek**: We have sent a query request for our own proposed lift along 
	the marked segment.  The lift has a UUID and a range of amounts we will 
	find acceptable.

- **pend**: We received a request for lift via a downstream foreign peer.
	Either:
	- We have knowledge of one or more pathways for the lift which connects 
	  with the intended recipient, a single, known, upstream foreign peer 
	  who holds a foil with one of our local users; or
	- We have discovered the intended recipient of the lift to be one of 
	  our local users.  If this is one of our own lifts, it just came full 
	  circle.  If not, our user is the end of a linear lift.
  
- **closed**: We have now upgraded our own prospective lift to a proposal 
	with a specific amount, and a token which can be used to validate a 
	final commit signature.

- **void**:	The lift has been abandoned by the originator.
  
- **timeout**:	Our request for lift has not been answered.  We will need a provision to retry or redirect to another pathway.

Obsolete States?
- **relay**:	We have forwarded our willingness and terms for a sought lift which was previoiusly in the query state.

- **invoice**:	Our local user has created a request to be paid through a linear lift.

- **propose**:	Our prospective lift has now been communicated upstream.

- **proffer**:	We have received an upgrade from downstream to a previous lift
  query that has not yet expired.  We accept the specific terms
  and choose to participate.  All we need now is a signature to
  make this binding money.
- **pending**:	We have sent the specific lift along upstream.  We expect to
  receive a final signature next to make this final.

### Chit Chains and Lifts
For an understanding of how chits are stored in a hash-chained linked list, 
please review [this section](learn-tally.md#chit-chains).

The lift and chit state machines are closely intertwined.  When a lift is
completed, we will be entering a series of chits on a number of local tallies
and expecting our peer sites to do so as well in a cascade of coordinated 
transactions.

In some respects, we want lift chits to be exempt from actions occuring in the
regular chit state diagram.  For example, if we create a draft chit, intended
to become part of an eventual lift, we don't want to start transmitting that
to peer sites.  And we don't want to create any triggers for the UI.

However, when it comes time to commit signed chits to tallies, there is no
guaranty that the two halves of the tally are in sync with each other at that
moment.  We need to be able to commit the chits and then trust the chit state
machine to clean up after us by inserting the chits into the hash-chain and
then communicating with their other half if necessary to resolve any conflicts
in the order of resulting chits.

### The Lift Record
A lift can either be linear or circular.  In the case of a circular lift, we 
need to keep track of:

  - The top peer in our segment (also the base of the external route)
  - The bottom peer in our segment (also the destination peer)
  - The set of local users in between (to know what chits to build)

It should be possible to discover multiple internal pathways that have the same 
top and bottom peer.  So we need a way to know which one was contemplated when 
the lift was initiated.

In the case of a linear lift, we must track:

  - The local user who is sending value (base of our local segment)
  - The intended recipient (for whom we probably don't have a user ID)
  - The top peer in our segment (also base of the external route)
  - The string of local users who will be part of the lift

In order to uniquely remember which users will be part of the lift, we should
probably store the path and tally-guid arrays.  That way, we won't need to
recompute pathways when it comes time to make chits.


If the lift was not initiated on our local system, it was propagated to us
from below.  In this case, the destination is either A or B:

- A: One of our users:
    - Linear lifts end with the destination user.
    - Circular lifts have one more chit to circle back to the originator.
  
- B: Not one of our users:
    - Circular or Linear, we treat it the same.  Compute the best local
      segment and pass the lift on to the best possible route anchored on
      that segment.

<br>[Next - Network Topology](learn-network.md)
<br>[Back to Index](README.md#contents)

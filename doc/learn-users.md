<div style="display: flex; justify-content: space-between;">
  <a href="README.md#contents">Back to Index</a>
  <a href="learn-tally.md">Next</a>
</div>

## Users and Identities

As discussed [previously](learn-general.md#money-as-credit), MyCHIPs implements
a monetary system based on <i>private</i> credit.
Due to its [fully decentralized](learn-general.md#decentralization)
design, MyCHIPs transactions are private--particularly when compared
with a <i>public</i> block chain.

### Private Credit Identities
One of the challenges with some credit-based systems relates to establishing a
genuine identity for each of the participants.  For example, what if someone
enters a credit pool with a false identity, creates a bunch of credit-based money,
and then leaves without standing behind those credits?

This problem is largely mitigated with MyCHIPs.
Users typically need only concern themselves with the credit-worthiness of those
they connect directly to (share a [tally](learn-tally.md) with).
Users are encouraged to connect only with people and companies they already have some 
degree of implicit trust in (such as employers, regular customers and regular suppliers).

Furthermore, users can [quantify and limit](learn-tally#credit-terms) the trust they
have for their partners so no one needs to take any more risk than a 
particular relationship warrants.

True, entities could potentially join the MyCHIPs network through multiple different 
relationships (and possibly even different identities).
But unless they can develop a sufficiently strong real-world reputation to earn a 
non-zero credit limit, they will be limited in the kind of damage they can inflict.

### Traditional Resource Addressing
We are familiar with the traditional Internet model where digital resources are
accessed using a public address in [URI](https://en.wikipedia.org/wiki/URI) format.
A host address is an important part of the URI which may also include a port number.
Host addresses are typically specified as a domain name or possibly an IP number.

IP numbers are a more <i>hard-coded</i> way of addressing resources.  More often
we prefer to use a logical domain name so that if we want to move a computer to a location
where the IP number is different, people can still address the information at the
expected place without having to know to change the host address to the new location.

Using DNS, the owner of the resource can just re-point the old domain name to the new IP
number and users will be able to access the same old information and the same old host
address, even though the IP number is completely different.

But this flexibility introduces a potential security problem.  When you connect to a given 
IP number, how can you know with certainty that the data you are accessing truly belongs to 
the owner of the intended domain?  What if your local DNS server fools you into visiting
an imposter IP number just so a phony site can harvest confidential information like your
passwords or account numbers?

This is where SSL certificates and the https protocol come in to offer the needed security.
But authority-based site certificates are not without their own set of problems.
They rely on a centralized, hierarchical authority to vouch for the authenticity of 
each digital resource you access.
There are a limited number of such authorities and their service tends to be available
only at a cost.

MyCHIPs emphasizes these important objectives:
- Users may not always want their identity to be publicly available.
  A public-facing company might want as many people as possible connected with
  a direct credit relationship.  But private users are more likely to want to stay
  that way--private.
- MyCHIPs is meant to be a fully decentralized, or <i>distributed</i> system.
  This is a conscious choice made to optimize the freedom and independence of users.
- MyCHIPs strives to operate independent of any authority, host, platform, operating
  system, or network.  It is simply a protocol systems can observe to 
  facilitate the exchange of value.

### Actors
For purposes of analysis and improved implementation, we will outline the following
conceptual <i>actors</i> and the various functions they are authorized to perform.

- User: A real-world entity (person or organization).
  An entity can have multiple users, similar to having multiple email addresses.
  Each user is associated with a particular private/public key pair.
  - Creates and shares tally invitations
  - Participates in tally invitations (proposes terms and identity information)
  - Accepts/signs proposed tallies
  - Initiates linear/payment lifts
  - Establishes/authorizes trading variables and other changeable tally parameters
- Store: A process authorized to maintain tally data on behalf of a user.
  - Responds to requests for tally invitations
  - Receives duly signed direct chits belonging to held tallies
  - Handles ACID transactions which conditionally promise/commit lift chits
- Agent:
  - Proposes routine clearing lifts
  - Responds to requests for lifts from connected peer users (promise/reject)
  - Honors a user's authorized tally parameters including trading variables
  - Signs lift transactions (commit/rollback)

### CHIP Addresses
MyCHIPs user entities (people and companies) can be reached using a _CHIP address_.

A fundamental part of the CHIP address is an agent ID (or just "agent") which 
represents a process (a program running on a computer) that handles transactions on 
behalf of one or more users.

Where an agent services multiple users, each user is referred to by a unique
CHIP User Identifier (CUID).
This can be thought of as a username on the agent system.
It is similar to the first part of an email address--the part prior to the '@' symbol.

### Agent Key
As mentioned, the agent ID is associated with a public key.
In early MyCHIPs implementations, the agent ID was generated simply by encoding
the agent's public key into base64url format.
While simple and elegant, this limited the system to use of a specific cryptographic algorithm.

As of November 2024, MyCHIPs will migrate toward using [libp2p](https://libp2p.io/)
for peer communications.
Therefore, the agent ID is now generalized to be a libp2p [peer ID](https://docs.libp2p.io/concepts/fundamentals/peers/).

The agent ID is no longer _the very_ public key, but is now a multihash derived _from the public key_.

This has several implications:
- The agent ID now can use a variety of hashing algorithms and formats.
- The ID can represent keys in virtually any algorithm (including post-quantum varieties).
- When peers negotiate a new connection, the actual public key must now be disclosed, in addition to the agent address.
- It may also be necessary to disclose one or more bootstrap peers (particularly to brand new users).

Implentation over libp2p has several advantages over the legacy design:
- Communications are not limited to noise protocol
- Communications are not limited to tcp/ip
- Agents can be located behind firewalls or reached through relays
- A large amount of complexity is removed from the code-base
- It may now be possible to implement a complete MyCHIPs service on a mobile device

### Legacy CHIP Addresses
In the legacy design, the CUID and agent formed a basic CHIP Address (CHAD) presented like this:
```
  suzie:6j9z7de95UMTnZzWobwtob6Mc3MDGDntdhSNR80pGXE
  6j9z7de95UMTnZzWobwtob6Mc3MDGDntdhSNR80pGXE		(single-user site)
```
It was also necessary to know a physical address which was understood to consist of
a host (IP address or hostname) and a TCP/IP port number.
This was rendered like this:
```
  mychips.net:57423
```
These two parts were put together to form a more explicit CHAD:
```
  suzie:6j9z7de95UMTnZzWobwtob6Mc3MDGDntdhSNR80pGXE@mychips.org:57423
```
Or a fully qualified CHAD URI as in:
```
  chip://suzie:6j9z7de95UMTnZzWobwtob6Mc3MDGDntdhSNR80pGXE@mychips.org:57423
```
The URI format had the potential for adding additional parameters in an optional
query string.  This could include things like a connection token, a peer name, or
other applicable information.

CHIP addresses (and other MyCHIPs message components) might also exist as a JSON (or similar data) structure.
For example:
```
  {
    agent: 6j9z7de95UMTnZzWobwtob6Mc3MDGDntdhSNR80pGXE,
    cuid: suzie,
    addr: /dns/mychips.org/ip/57423
  }
```
In prior versions, this structure could include the properties _host_ and _port_.
Those properties are deprecated in favor of the new, optinoal _addr_ multiaddress property.

### CHIP Addresses With Libp2p
Under libp2p, a peer's logical address is its peer ID.
But its physical address is specified as a [multiaddress](https://docs.libp2p.io/concepts/fundamentals/addressing/) as follows:
```
  /dns/mychips.org/tcp/57423
```
The CHIP address might be expressed as a multiaddress like so:
```
  /chip/6j9z7de95UMTnZzWobwtob6Mc3MDGDntdhSNR80pGXE/cuid/susie
```
And these can be combined for a full address as follows:
```
  /dns/mychips.org/tcp/57423/chip/6j9z7de95UMTnZzWobwtob6Mc3MDGDntdhSNR80pGXE/cuid/susie
```
Most users don't need to concern themselves much with physical addresses.
Most often, peers will be identified by their peer ID and physical addresses can be discovered in real time as needed.

This allows peers to change physical addresses or even to roam about the network.

<div style="display: flex; justify-content: space-between;">
  <a href="README.md#contents">Back to Index</a>
  <a href="learn-tally.md">Next</a>
</div>

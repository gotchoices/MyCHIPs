<div style="display: flex; justify-content: space-between;">
  <a href="README.md#contents">Back to Index</a>
  <a href="learn-tally.md">Next</a>
</div>

## Users and Identities

As discussed [previously](learn-general.md#money-as-credit), MyCHIPs implements
a monetary system on the basis of <i>private</i> credit.

Due to the [decentralized](learn-general.md#decentralization) nature of its
design, the transactions themselves become quite private as well--certainly much
more private than we can achieve with a <i>public</i> block chain.

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

### Traditional Resource Addresses
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

This problem was largely solved by introducing SSL certificates and the https protocol.
But this solution is not without its own set of problems.

MyCHIPs emphasizes two important objectives:
- First, users may not always want their identity to be publicly available.
  A public-facing company might want as many people as possible connected with
  a direct credit relationship.  But private users are more likely to want to stay
  that way--private.
- Second, MyCHIPs is all about decentralization.  This is a conscious choice made to
  optimize the freedom and independence of users.  Unfortunately, DNS and https, rely
  on a centralized, hierarchical authority to vouch for the authenticity of each digital 
  resource you access.
  There are currently a limited number of these authorities established in a reliable 
  way and you typically have to pay one of them to participate.

MyCHIPs is designed to work with <i>or without</i> DNS.  And user addresses are meant
to be private unless and until the owner chooses to make them known.

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
The URI format has the potential for adding additional parameters in an optional
query string.  This could include things like a connection token, a peer name, or
other applicable information.

A CHIP address (and other MyCHIPs message components) may be presented as a JSON (or similar data) structure.
For example:
```
  {
    cuid: suzie,
    agent: 6j9z7de95UMTnZzWobwtob6Mc3MDGDntdhSNR80pGXE,
    host: mychips.org,
    port: 57423
  }
```

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

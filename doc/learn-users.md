## Users and Identities

As discussed [previously](learn-general.md#money-as-credit), MyCHIPs implements
a monetary system on the basis of <i>private</i> credit.

Due to the [decentralized](learn-general.md#decentralization) nature of its
design, the transactions themselves become quite private as well--certainly much
more private than we can achieve with a <i>public</i> block chain.

### Identities
One of the challenges with some credit-based systems relates to establishing a
genuine identity for each of the participants.  For example, what if someone
enters the system with a false identity, creates a bunch of credit-based money,
and then leaves without standing behind those credits?

This problem is largely eliminated in MyCHIPs.  Only the people who connect
directly with each other need to be concerned with the identity of their trading
partners.  And users are encouraged to connect only with people and companies
they already have some degree of implicit trust in.

Furthermore we will [quantify and limit](learn-tally#credit-terms) that trust in each
of the trading relationships so no one needs to take any more risk than a particular
relationship might warrant.

True, entities could potentially join the MyCHIPs network through multiple different 
relationships (and possibly even different identities).
But unless they can develop a sufficiently strong real-world reputation to earn a 
non-zero credit limit, they will be very limited in the kind of damage they can inflict.

### Resource Addresses
Our Internet experience makes us familiar with a model where digital resources are
accessed using some kind of public address such as a [URI](https://en.wikipedia.org/wiki/URI).
A host address is an important part of the URI which may also include a port number.
Host addresses are typically specified as a domain name or possibly an IP number.

IP numbers are a rather <i>hard-coded</i> way of addressing resources.  More often
we prefer to use a logical domain name so that if we want to move a computer to a location
where the IP number is different, people can still address the information at the
expected place without having to know to change the host address to the new location.

Using DNS, the owner of the resource can just re-point the old domain name to the new IP
number and users will be able to access the same old information and the same old host
address, even though the IP number is completely different.

This flexibility introduces a potential security problem.  When you connect to a given 
IP number, how can you know with certainty that the data you are accessing truly belongs to 
the owner of the intended domain?  What if your local DNS server fools you into visiting
an imposter IP number just so a phony site can harvest confidential information like your
passwords or account numbers?

MyCHIPs includes two important objectives:
- First, we don't always want user information to be publicly available.
  A public-facing company might want as many people as possible connected with
  a direct credit relationship.  But private users are more likely to want to say
  that way--private.
- Second, MyCHIPs is all about decentralization.  This is a conscious choice made to
  optimize the freedom and independence of its users.  Under DNS, you have to rely on 
  some authority to vouch for the authenticity of each digital resource you access.
  There are currently a limited number of these authorities established in a reliable 
  way and you typically have to pay one of them to participate.

MyCHIPs is designed to work with or without DNS.  And user addresses are meant
to be private unless and until the owner chooses to make them known.

### CHIP Addresses
On the MyCHIPS network, entities (people and companies) are referred to by a
CHIP Identifier (CID) which can best be thought of as a unique username on their
host system.  It is analogous to the first part of an email address--the part prior
to the '@' symbol.

In most cases, the CID will be combined with an agent ID (or just "agent") that
represents the public key of a server process that handles business on behalf of
the MyCHIPs user.

Together, the CID and agent form a more complete MyCHIPs address that may be
presented like this:
```
  suzie:6j9z7de95UMTnZzWobwtob6Mc3MDGDntdhSNR80pGXE
```
Note: the term "agent" is used here in a different context than the 
[agent-based model](sim-agent.md) that is used as part of the simulation environment
for testing and evaluating MyCHIPs.
In this context, it simply means a software service that acts on behalf of one or more
users on a host site.

### Portals
Notably, the CHIP address is missing any kind of location information that might help us
find this user on the Internet.  That is by design to facilitate a greater degree of
privacy and decentralization.

But a MyCHIPs user will have to divulge location information of some kind--at least
to his expected trading partners.  So there is more we can add to the CHIP address to make
it clear where other users can connect.

This additional information consists of a regular host address and a port number.
In web technology, this is often called an "origin" and it is rendered like this:
```
  mychips.org:57423
```
We can put these two pieces of information together, separated by an '@' symbol, to 
form a more explicit address as in:
```
  suzie:6j9z7de95UMTnZzWobwtob6Mc3MDGDntdhSNR80pGXE@mychips.org:57423
```
We can form a fully qualified URI as in:
```
  chip://suzie:6j9z7de95UMTnZzWobwtob6Mc3MDGDntdhSNR80pGXE@mychips.org:57423
```
This also provides the potential for adding additional parameters in an optional
query string.  This might include things like a connection token, a peer name, or
other applicable information.

The CHIP address (and other MyCHIPs message components) may optionally be encoded as a JSON (or other) structure.
For example, we might see a CHIP address presented as something like:
```
  {
    user: suzie,
    agent: 6j9z7de95UMTnZzWobwtob6Mc3MDGDntdhSNR80pGXE,
    address: mychips.org,
    port: 57423
  }
```
Note: we expect a one-to-one relationship between an agent and its portal.
That is, an agent with a particular key value should be reachable on a single portal. 
And a portal address should serve one and only one agent.

### Obscured CID
The CHIP address convention also allows a CHIP ID to be made more private by specifying it
as a hash that only the host site will recognize.  For example, a user might be
asked to send money to an address such as:
```
  aGxz38Dyylkj:6j9z7de95UMTnZzWobwtob6Mc3MDGDntdhSNR80pGXE
```
This presumes the specified agent is part of a site that can recognize 'aGxz38Dyylkj'
as meaning 'suzie'.

The sender (and even the sender's host system) may have no way of knowing who the 
target user is or what system hosts his service.  Yet, they can still transact a
payment to the correct destination.

### Exposed Addresses
In some cases it may be helpful to be more clear about the affiliation associated 
with a CID.  For example, it might be specified like this:
```
  suzie@mychips.org
```
Keep in mind that a system would likely have to rely on a 
[certificate authority](https://en.wikipedia.org/wiki/Certificate_authority) to 
securely contact mychips.org, somehow obtain a connection public key and portal, and 
then carry out the connection.

It is unclear (at the time of this writing) whether this notation will be useful.
But the most likely scenario would be when specifing a
[linear lift](learn-lifts.md#linear-lifts) payment.  The point would be to expect
some peer site along the way to recognize the username and domain address and
already know the correct agent key and port number.

This form also has the desirable side effect of allowing certain sites to correlate
CHIP addresses directly with their users' email addresses.

### Explicit Agent Addresses
In some parts of the protocol, it may be helpful to specify the agent and portal
only (i.e. no particular user).  For example, a [lift](learn-lifts.md) initiator may 
want to publish a portal where it can be contacted to obtain information about a 
pending lift.

Such information would necessarily include a connection key so as to guarantee that
the correct host has been reached.  This might look like:
```
  6j9z7de95UMTnZzWobwtob6Mc3MDGDntdhSNR80pGXE@mychips.org:57423
```

### Agent Key
As mentioned, the agent is identified by a public key.
To create the Agent ID, we encode the public key according to a 
[variant of base 64](https://datatracker.ietf.org/doc/html/rfc4648#section-5).

A client can decode this public key and use it to validate a connection at the
specified port.  This will ensure that the process answering on the other end of the
port is really controlled by the private key associated with the specified agent
public key.

This provides several benefits:
- The agent ID serves as a logical address of sorts, akin to a domain name, but which is
  not automatically known to the public.
- Peers can share portal information with each other as needed to facilitate private
  connections.
- Portal specifications can specify a host address as a domain name or as an IP number.
  If a domain name is specified, the agent key will protect the connection initiator
  from being spoofed by an imposter site.
- If the portal is specified by IP number, the site can change to a new IP number 
  later as long as it communicates to a finite set of trading partners where the
  new portal is for future connections.

<br>[Next - The Tally](learn-tally.md)
<br>[Back to Index](README.md#contents)

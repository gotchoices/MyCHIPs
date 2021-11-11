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

Furthermore we will quantify and limit that trust in each of the trading
relationships so no one needs to take any more risk than a particular relationship
might warrant.

The result is, individuals could potentially join the MyCHIPs network in multiple
different locations, each one with a different set of trading relationships.
But unless they can develop sufficient real-world reputation to earn a non-zero credit
limit, they will be very limited in the kind of damage they can inflict.

### Site Addresses
In the Internet age, we are familiar with a model where digital resources are
accessed using some kind of public address such as a [URI](https://en.wikipedia.org/wiki/URI).
An important part of the URL is a host address and can include an optional port number.
Host addresses are typically specified as a domain name or possibly an IP number.

IP numbers are a rather <i>hard-coded</i> way of addressing resources.  More often
we prefer to use a logical domain name so that if we want to move a computer to a location
where the IP number is different, people can still address the information at the
expected place without having to know to change the host address to the new location.

Usins DNS, the owner of the resource can just re-point the old domain name to the new IP
number and users will be able to access the same old information and the same old host
address, even though the IP number is completely different.

This flexibility introduces a security issue.  When you connect to a given IP number, how
can you know with certainty that the data you are accessing truly belongs to the owner
of the domain you are searching for?  What if your local DNS server fools you into visiting
an imposter IP number just so a phony site can harvest confidential information like your
passwords or account numbers?

Under MyCHIPs, we have two important objectives:
- First, we don't always want user credit information to be publicly available.
  A public-facing company might want as many people as possible connected with
  a direct credit relationship.  But private users are more likely to want to say
  that way--private.
- Second, MyCHIPs is all about decentralization.  This is a conscious choice made to
  optimize the freedom and independence of its users.  Under DNS, you have to rely on 
  some authority to vouch for the authenticity of each digital resource you access.
  There are only so many of these authorities established in a reliable way so you
  will have to pay one of them to participate.

So MyCHIPs data is designed to work with or without DNS.  And user addresses are meant
to be private unless and until the owner explicitly grants access to them.

### CHIP Identifier
Entities (people and companies) on the MyCHIPs network are referred to by a
CHIP Identifier (CID) which is a unique combination of a:
- Username; and
- Proctor ID

The username can be any string that is uniquely recognized within the site hosting
the user's account.  The proctor ID (or just "proctor") is a public key that will be
used in verifying the authenticity of the data once a peer makes a connection to the
user's account.

The username and proctor are typically separated by a colon (:) and might look
something like this:
```
  suzie:6j9z7de95UMTnZzWobwtob6Mc3MDGDntdhSNR80pGXE
```

### Portals
Notably, the CID is missing any kind of location information that might help us
find this user on the Internet.  That is by design to facilitate a greater degree of
privacy and decentralization.

But a MyCHIPs user will have to divulge location information of some kind--at least
to his expected trading partners.  So there is more we can add to the CID to make
it clear where other users can connect.

This additional information consists of a regular host address and a port number,
also separated by a colon as in:
```
  mychips.org:57423
```
We put these two pieces of information together, separated by an '@' symbol, to form 
a more explicit CID as in:
```
  suzie:6j9z7de95UMTnZzWobwtob6Mc3MDGDntdhSNR80pGXE@mychips.org:57423
```
We can form a fully qualified URI as in:
```
  mychips://suzie:6j9z7de95UMTnZzWobwtob6Mc3MDGDntdhSNR80pGXE@mychips.org:57423
```
This also provides the potential for adding additional parameters in an optional
query string.  This might include things like a connection token, a peer name, or
other applicable information.

The CID (and other MyCHIPs message components) may optionally be encoded as a
JSON structure.  For example, we might also see a CID presented as something like:
```
  {
    user: suzie,
    proctor: 6j9z7de95UMTnZzWobwtob6Mc3MDGDntdhSNR80pGXE,
    address: mychips.org,
    port: 57423
  }
```

### Obscured Usernames
The CID convention also allows a username to be made more private by specifying it
as a hash that only the host site will recognize.  For example, a user might be
asked to send money to an address such as:
```
  aGxz38Dyy:6j9z7de95UMTnZzWobwtob6Mc3MDGDntdhSNR80pGXE
```
This presumes the specified proctor is part of a site that can recognize 'aGxz38Dyy'
as meaning 'suzie'.

The sender (and even the sender's host system) may have no way of knowing who the 
target user is or what system hosts his service.  Yet, they can still transact a
payment to the correct destination.

### Generic Addresses
In some cases it will be helpful to be more clear about a payment address.
For example, in some instances, a CID might also be specified like this:
```
  suzie@mychips.org
```
Keep in mind that a system would likely have to rely on a 
[certificate authority](https://en.wikipedia.org/wiki/Certificate_authority) to contact
mychips.org, somehow obtain a connection public key and portal, and then carry out
the connection.

It is unclear at the time of this writing whether this notation will be useful.
But the most likely scenario would be when specifing a
[linear lift](learn-lifts.md#linear-lifts) payment.  The point would be to expect
some peer site along the way to recognize the username and domain address and
already know the correct proctor key and port number.

It also has the desirable side effect of certain sites correlating CID's directly
with their users' email addresses.

### Site Addresses
In some parts of the protocol, it may be helpful to specify the proctor and portal
only.  For example, a [lift](learn-lifts.md) initiator may want to publish a portal
where it can be contacted to obtain information about a pending lift.

Such information would necessarily include a connection key so as to guarantee that
the correct host has been reached.  This might look like:
```
  6j9z7de95UMTnZzWobwtob6Mc3MDGDntdhSNR80pGXE@mychips.org:57423
```

### Proctor Key
As mentioned, the proctor is really just a public key but it has been encoded
according to a [variant of base 64](https://datatracker.ietf.org/doc/html/rfc4648#section-5).

A client can decode this public key and use it to validate a connection at the
specified port.  This will ensure that the process answering on the other end of the
port is really controlled by the private key associated with the specified proctor
public key.

This provides several benefits:
- The proctor serves as an logical address of sorts, akin to a domain name, but which is
  not automatically known to the public.
- Peers can share portal information with each other as needed to facilitate private
  connections.
- Portal specifications can specify a host address as a domain name or as an IP number.
  If a domain name is specified, the proctor key will protect the connection initiator
  from being spoofed by an imposter site.
- If the portal is specified by IP number, the site can change to a new IP number 
  later as long as it can communicate to a finite set of trading partners where the
  new portal is for future connections.

<br>[Next - The Tally](learn-tally.md)
<br>[Back to Index](README.md#contents)

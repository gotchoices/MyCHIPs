## Data Message Encoding
Feb 2022; Copyright MyCHIPs.org

### General
A MyCHIPs network potentially consists of many different processes running on many different machines.
A single site is modeled as shown here:

[![System Design](uml/scaling.svg)](uml/scaling.svg)

The different components of the system will communicate with each other by passing messages encoded as JSON packets.
The common cases, covered in previous sections, are:
- User application <-> User service / Database; [see](use-mobile.md#user-api-objects)
- Database <-> Agent service
- Peer Agent service <-> Peer Agent service (peer-to-peer)

In general, the user application will interact with the system by doing one of the following:
- Sending an SQL command, encoded in a JSON record, to the database;
- Invoking a control layer action handler, which will likely further interact with the database.

The mobile application will generally not be able to interact with a peer agent module as this may be
an entirely separate process from the User service.

### Message Targets
Communications related to peer agent services are handled by one of four different subsystems as follows:
- tally
- chit
- route
- lift

Most messages in the following cases will have a property called "target" containing the
name of the applicable subsystem.  The primary exception is in communication from the
agent process to the database since the subsystem is already inherently known by the
database procedure being called.

### Agent Server with Database
When the model state changes in the database, it may detect certain events that require
action from the user or the agent server.  Events meant for an agent server are managed by 
generating an asynchronous notification using the tag:
```
  mychips_agent_AGENT_PUBLIC_KEY
```
where AGENT_KEY_PUBLIC key indicates the agent address for the process responsible for
traffic for the applicable user.  The notification will also contain a JSON encoded message.

The agent service will likewise receive events from other peer agents that need to be communicated 
to the model.  These events are managed by issuing an SQL query to a stored procedure in the
database with a JSON encoded message as one of the parameters.

### Message Format
Messages from one agent to another peer agent are sent over [noise protocol](learn-noise.md#noise-protocol-implementation)

Messages are currently encoded as JSON structures.  Future implementations might move to a 
more compressed binary form (or at least a form where properties are much more abbreviated.)
But the current form is quite human-readable and so may be used for some time--particularly in 
testing/validation phases.

Messages destined for another user's agent will typically have the following basic properties:
- **target**: What kind of object (subsystem) the message applies to.  For example, tally, chit, route, lift.
- **action**: A code representing what step or function is being requested or communicated via the packet.
  This may well be the name of state that is being suggested as the next step in a negotiation.
- **object**: The contents of the object (tally, chit, route, lift) itself.
- **try**: An integer starting at 1 indicating how many times the sender has tried to send this message.
- **last**: A timestamp for when the message was generated.
- **to**: The [CHIP Address](learn-users.md#portals) of the recipient, containing some or all of the following, as applicable:
  - **cid**: The [CHIP ID](learn-users.md#chip-addresses) of the sender.
  - **agent**: Encoded agent public key
  - **host**: Hostname or IP number
  - **port**: Port to connect on
- **from**: The [CHIP Address](learn-users.md#portals) of the sender, containing some or all of the following, as applicable:
  - **cid**: The [CHIP ID](learn-users.md#chip-addresses) of the sender.
  - **agent**: Encoded agent public key
  - **host**: Hostname or IP number
  - **port**: Port to connect on

Once an agent receives a message, it may trim the message to only those properties that are required before
forwarding the message on to the database.  Some fields not ever required by the database include:
target, action, from, last, try.

Some messages from the agent to the database are intended to insert or update the content of the object
(tally, chit, route, lift) itself.  These messages must include the object property in its full
JSON exchange format.  In simpler cases, a message may only need to change the status of the object
(for example, voiding or closing) so the whole object may not be necessary.  However, at a minimum
the object will have to contain any identifiers (uuid, for example) needed to uniquely locate the
object in the database.

### Tally Messages
Property: **target**: tally

The *object* property for the tally is defined as follows:
  - **version**: Version (1) of the tally format.
  - **foil**: The [CHIP ID](learn-users.md#chip-addresses) of the customer/employer/client.
  - **stock**: the CHIP ID of the provider/employee/vendor.
  - **uuid**: A [Universally Unique Identifier](https://en.wikipedia.org/wiki/Universally_unique_identifier) for this particular tally.
  - **comment**: Any comments to the tally the parties have agreed to include.
  - **created**: Date/time the tally was created
  - **contract**: The general terms and conditions of the credit agreement.
    - **name**: Issuer/author of the tally contract language
    - **version**: Version of the contract
  - **terms**: An object containing [credit variables](learn-tally.md#credit-terms)
  - **signed**:
    - **digest**: A string hash of the rest of the tally in a standard serialized format
    - **foil**: The digital signature of the hash by the foil holder (client)
    - **stock**: The digital signature of the hash by the stock holder (vendor)

Tally state transition messages are as follows:
- *DB->Agent, Agent->Agent;* **Initiate Tally Connection**;
  The process is responding to a tally invitation by
  requesting that a connection be opened to the site containing the tally and asking
  that the actual tally draft be sent back.
  - **action**: ticket;
  - **ticket**: a connection ticket (i.e. not a tally yet!) containing:
    - token: connection code
    - cert: CHIP certificate of the subject peer who will receive the tally

- *DB->Agent:* **Request Agent to Send a Draft Tally**;
  The DB requests the agent to send the contained tally proposal to the requester or intended partner.
  - **action**: userDraft

- *Agent->Agent:* **Sending a Draft Tally Offer**;
  A peer agent is sending the contained tally intending to execute on the proposed terms.
  - **action**: peerProffer

- *DB->Agent:* **Request Agent to Refuse Tally**;
  The DB requests the agent to tell the prospective partner of the tally "no thanks."
  - **action**: userVoid

- *Agent->Agent:* **Refusing a Draft Tally Offer**;
  A peer agent is indicating that the referenced tally has been refused by its user.
  - **action**: peerRefuse

- *DB->Agent:* **Request Agent to Accept Tally**;
  The DB requests the agent to tell the prospective partner of the contained, signed tally "I accept."
  - **action**: userAccept

- *Agent->Agent:* **Accepting a Draft Tally Offer**;
  A peer agent is transmitting a tally that has been accepted and signed by its user.
  - **action**: peerAccept

- *DB->Agent:* **Request Agent to Notify of Tally Close Request**;
  The DB requests the agent to tell the partner of the current tally that it has been marked by our user to be closed upon attaining a zero balance.
  - **action**: userClose

- *Agent->Agent:* **Marking a Tally for Closing**;
  A peer agent is indicating that the referenced tally has been marked for closure by its user.
  - **action**: peerClose

### Chit Messages
*Under Construction*

### Route Messages
*Under Construction*

### Lift Messages
*Under Construction*

<br>[Next - Hacking](work-hacking.md)
<br>[Back to Index](README.md#contents)

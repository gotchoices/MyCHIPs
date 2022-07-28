## Upgrading the Software

As with any software service, it becomes necessary from time to time to install
the latest version of the software.

For small or self-hosted systems, this may not be a big deal.  We can just turn
the system off, do the upgrade and then turn it back on.

But in larger production systems, upgrades may pose a bigger challenge.  We 
would like to maintain availability to the user application at all times so 
when someone pushes the "pay" button, the backend server is ready to perform 
the associated action.

Even more importantly, we expect a whirlwind of lifts to be constantly spinning
through the network.  One particular site may have many lifts in process at any
given moment.  It would be difficult to find a convenient moment to shut down
a database for maintenance.  And if we did, all the users on that site would
lose access to valuable lift opportunities as long as the system was down.

The goal is to design a system that can get as close to 100% uptime as 
possible, and to have a strategy for software updates that creates the smallest
possible disruption to the overall user experience.

### General Architecture

The system is designed with a PostgreSQL (PG) database at the center.  This is 
where the authoritative state of the system is maintained.

There can also be any number of JavaScript servers associated with a single PG
instance.  Most notably are these:
  - User Server (whether SPA for a web app, or NoiseProtocol for a native app)
  - Peer Server

Ideally, these processes should be completely stateless.  Their job is to 
receive and send packets on a specified port, handle various tasks of 
authentication, parsing, and encryption.  They also relay messages to/from the 
PG instance as needed.

If one of these processes gets shut down in the middle of a transaction, the
damage should be limited to requiring a retry of some kind with the associated
peer or user application.  But the database should be synchronous and atomic.
If a change in state succeeds, the database will have it.  If it does not go
through, the database will still be in the prior, consistent state and a retry
process can keep iterating until everything works out OK.

### Upgrading the Database

There are two issues surrounding the backend database:
  - The PostgreSQL server itself (version 11, 12, etc.)
  - The MyCHIPs schema design

In short, we would like to be able to upgrade either of these without losing
availability.  In a high availability setting, we would:
  - Run two or more PG servers with synchronous replication
  - Have one server at any given moment as the master
  - Keep one or more other servers as hot standby's

For regular maintenance, we can switch over to a backup server, work on the old
master, and then switch back when ready.  During this down cycle, we could even
install a later version of the server software.  This should make upgrades
appear seamless from the user perspective.

With the right external configuration, it should also be possible to use a hot
standby to do automatic failover should the master server crash for some
reason.

### Upgrading the Schema

The intent here is to use Wyseman in such a way that we never really have to
turn off the database to do an upgrade.  Wyseman is designed (work in process
to be able to modify a database schema in a transaction.  This can even include 
dropping and rebuilding whole tables.

This will consume some time--particularly when tables get larger.  But if any
given transaction is not too large, it should just look like an unusually long
delay on certain requests sent to the DB.

The biggest challenge will be:  Yes, we can update the schema on the fly.  But
what if the schema changes so much that it is no longer compatible with the JS
server running in the middle?

For example:
  - We are running along with both PG and servers on version 2.0
  - We want to upgrade to 3.0
  - We launch the 3.0 server, it detects the change in version and upgrades
    the PG schema on the fly.
  - All is good with that server, but if we have any old stray 2.0 processes
    still around, they may be talking to a 2.0 backend one moment and a 3.0
    the next.

So we will need a way to:
  - Orderly shut down all servers connected to a single PG instance,
  - Launch one back up of the new version, which will grab the database and
    initiate the upgrade,
  - Quickly launch any others we may need (for example, on other ports) so
    they can at least answer port traffic, even if they have to wait some
    seconds for the new schema to become available for their queries.

<br>[Next - FAQ](ref-faq.md)
<br>[Back to Index](README.md#contents)

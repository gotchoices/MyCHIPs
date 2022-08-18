## Frequently Asked Questions

### Introduction
Often, when a developer reviews this (or any) project, they start out by 
wanting to change the way it has been implemented.  While I don't doubt there 
are many other good ways the project could have been done, I have made the best 
choices I could given the project requirements.

It is often said:
  "To him who has a hammer, everything looks like a nail."

While I have relied on a few of my "old favorite" hammers, I have tried to
concentrate on just picking the right tool for each part of the job.

In any case, I don't think it would be constructive to back up or start over on 
significant parts of the toolchain right now.  Rather, the best pathway forward 
is to get this reference implementation working as well as possible using its 
current implementation design.  When that works, there will be more time and 
motivation for other possible "from-scratch" versions to come along that might 
be more elegant or efficient.

### Couldn't you build MyCHIPs on top of (Etherium, holochain, other favorite blockchain thing...)?

Possibly.  Maybe somehow, but why?

Blockchain uses a de-centralized database topology.  But in many ways it is
still quite centralized.  Transactions must all go through a single, common, 
public store.  In contrast, MyCHIPs uses a fully distributed data model.
There is no double-spending problem or even a need for a public ledger.
So there is no need for Proof of Work or Proof of Stake.  Even the need for 
verifiable public identities has been largely eliminated.

The part of blockchain technology that _is_ applicable is the notion of chained
hashes.  MyCHIPs does make use of them (chit-chains) but it is implemented 
inside the database so there is not really a huge benefit in trying to coerce
the algorithm onto another framework.

Of existing technologies, the Holochain platform looks closest to possible.
But even as de-centralized as it is, it still seems designed more for 
information that requires a public view.  There is an aspect of MyCHIPs that
could benefit from that (as well as digital identies).  For example, if you get
disappointed by someone in a credit relationship, it could be helpful to 
publish a critical review so others can avoid the same pitfall.  However, that
is separate from the primary function of MyCHIPs--to transfer value through a
web of locally interconnected peers.

For those who insist that MyCHIPs be build "on top of something else":
Sorry, I've tried.  But "from scratch" was the best way I could find to get the
job done according to the critical principles.  It is difficult to model 
relativity using Newtonian physics.  Time and space start to break down.  
Likewise, it is hard to model private credit in the context of equity-based 
notions (like public ledgers, reputation-based trust, and the like).  Those are 
helpful constructs--just not directly applicable to a fully distributed money system 
based on private credit.

### Why use Javascript on the backend?

The asynchronous character of Javascript is key to the way the server runs.  A
single process can be started which is really several servers in one.  Or, many
processes can be launched with a more singular purpose to each one.  This could
be more challenging to achieve in a single-minded or threaded model.

Javascript was not my first impulse.  In fact, I had previously used it only as 
a "necessary evil" once in a while to automate web pages.  But after a couple of
attempts to code the server in synchronous languages, I quickly decided that
learning Node.js would be worth the investment.  I am convinced, it was a good
choice.

### Why use Vuejs?

In terms of the choice between React, Angular and Vuejs, I chose Vuejs simply
because it is lighter and much less opinionated.  I have too many of my own
opinions to have to argue with my programming language all the time.

More generally: the UI developed so far is primarily for my benefit as a 
developer.  While the admin console could be used in production, that is not 
necessary.  I hope and expect other UI's to be developed after the middle and 
back is proven functional and effective.

Certainly the end-user UI will need to be a user-friendly mobile app.  Whether
that is done in Vuejs, NativeScript, Native Apple/Android coding, or something
else  is yet to be determined.  For now, the user UI is simply a data-centric 
way to see and access the resources expected to be available to a user in the 
eventual production UI.

### Why use PostgreSQL?

First requirement of the system was that it be ACID.  There are transactions
coming into the model from all different directions and commits need to be
fully atomic (all-or-nothing).

PostgreSQL is at least as good as any other alternative in this category, if
not the best.  Furthermore, it turns out SQL (sometimes recursive SQL) is a
very effective way to compute the distributed routes for credit lifts.

I often get pressure to use No-SQL or even a graph database.  Mongo works
well enough for modeling the "real world" in the Agent simulation.  But it is
not the tool to do the job Postgres is doing as the core of the server model.

The graph databases I looked at would hold the model quite well, but there is
still the problem of analyzing the data.  I didn't want to reinvent the wheel
when a few well crafted SQL views could do the job so nicely.

In many cases, the ability to store/retrieve data as JSON is a big help to the
Nodejs server process (and the front end).  While Mongo would do that part very 
well, Postgres has good enough JSON functionality to fill the gap.

### What is all this Wy* stuff?

Wyatt-ERP is a group of libraries I developed some years ago which provide for
rapid development of database applications.  It was originally implemented in 
TCL/TK for use PostgreSQL.  I ported the parts that were most useful to develop
MyCHIPs.  This (an "old hammer") involves 4 npm libraries:

  Wylib: Front End UI library, partially ported to Vuejs
  Wyseman: Schema manager and database API gateway
  Wyclif: Control layer interface and application glue
  Wyselib: ERP schema library, partially ported

### Why use Wyatt-ERP?

Because I wanted to use PostgreSQL and Wyseman is the easiest/best way I know 
to do SQL development in a stable, extendable and repeatable way.

The Postgres backend is very much more than a set of tables to store data.  It
also includes a user/permission structure and many stored functions, triggers
and so forth.  Most of the algorithm is implemented inside the database itself.

To develop that, make changes, and keep everything in synch can be quite a
challenge (and one of the reasons people get frustrated with SQL databases).
Wyseman makes that much more convenient--even possible in this case.

### Can I use MySQL (SQLlite, etc.)

No.  PostgreSQL is doing so much more than just storing data in tables.  It is 
both a model and a state controller.  There is no compelling reason to try to 
accommodate more than one such platform.

Switching to another database would be nearly starting over from scratch.

### Why is your code so tightly packed?

Sorry, that's how I code.  It is easier for me to understand the code structure
when I can see larger parts of the logic flow in one page.  Each line tends to
be more concentrated than in other code you may see.  And I don't get paid by 
the line.  Unfortunately, I don't seem to be getting paid at all!

I also code a lot wider than 80 columns.  Assuming you're not still using a
VT100 or a teletype, make your window wider.  It will work.

### Will it run on Windows?

Sure.  In Docker!

In all seriousness, maybe.  But I haven't spent any effort trying this.  The
core of the system is implemented in PostgreSQL and Node, so running natively
on Windows could very well be possible.

The support scripts and simulation environment make heavy use of Bash.  So you 
would likely have to have that installed.  

If anyone wants to test/validate on Windows, your help would be welcome.

### Is there an API?

Absolutely, but possibly not what you're used to if you think API implies 
something implemented on top of HTTP.

The user API could be described as a CRUD+ interface (CReate, Update Delete).
The "plus" means there are some reports and stored functions that can also be
accessed.

The goal is, if you can connect to the database as a particular user, there are
a handful of views and functions the DB will allow you to use.  Whatever you
can read/write/execute over that interface constitutes the API.

The current SPA server creates a buffer for that API so you can connect using
a one-time token, which gets converted to a private connection key.  The
server validates you and then allows you to interact with the database by
sending queries that are represented as JSON structures (hey, kind of like
No-SQL!).  The data comes back to you as JSON as well so you can almost pretend
you're talking to Mongo.

### Why not implement this as a more standard web protocol?

That's probably code for: Why didn't you implement this on top of HTTP?

MyCHIPs is making every effort to not just de-centralize the monetary function, but
to make it fully distributed.
It is a lot easier to code using centralized thinking.
De-centralized is harder.
Distributed is even harder than that.

HTTP was built for the purpose of requesting web pages in a client/server model.
Yes, it was since extended to accommodate more authentic two-way data communications.
But it still has a fair amount of legacy overhead related to the way web browsers work.
In short, HTTP is a hammer and MyCHIPs is not a nail.

The way HTTP endpoints are defined and then proven authentic via DNS and a 
hierarchical certificate authority system is, by definition, centralized.

MyCHIPs uses standard IP numbers with optional host names.
So it can be used with or without DNS.
This allows the system to work in the absense of a central certificate authority scheme.

MyCHIPs also uses IP sockets in a pretty standard way, albeit at a lower level than most people are used to.
But connections are authenticated using distributed public/private key pairs as opposed to usernames and passwords.

Furthermore, network nodes are not typically found at known, public locations.
Certain site locations may only be known to their immediate trading partners.

These design choices were not made out of ignorance nor merely to be different.
Rather, they exist to accomplish very specific, critical, strategic performance objectives.

<br>[Next - Source Tree](ref-source.md)
<br>[Back to Index](README.md#contents)

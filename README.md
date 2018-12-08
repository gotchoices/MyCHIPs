# MyCHIPs
MyCHIPs is an open-source network for implementing digital money based on private credit.

This is *not* a Bitcoin/blockchain derivative, but rather it seeks to address
several serious problems inherent with those technologies.

Briefly, if block-chain based coins can be thought of as a crypto-stock
or crypto-equity, MyCHIPs can be characterized as a crypto-bond.  Either _can_
be used as a currency, or medium of exchange.  However, a credit-based 
solution will be much more resilient to such forces as speculation,
volatility, inflation, and deflation.  So it would be much better solution
when considering the three primary purposes of money:
* a medium of exchange,
* a store of value, and 
* a measure of value.

For more in-depth information, please visit [this site.](http://gotchoices.org/mychips/index.html)

### Project Background:
In 2017, I posted this as an empty project on [github](http://github.com/gotchoices/mychips)
hoping to attract a team of participants.  But there was not much traffic, and less interest.
So I began programming the project myself.

Initially, this involved reviving some old tools I have successfully used on other projects in the past:
Specifically, [Wyseman](http://github.com/gotchoices/wyseman) and
[Wyselib](http://github.com/gotchoices/wyselib) for deployment of a backend database, and
[Wylib](http://github.com/gotchoices/wylib) for a frontend GUI.

While Wylib is probably not the best solution for an eventual user GUI, it will do well
for an administrative console.  And it will suffice for a user SPA until a dedicated mobile
app can be built.  Besides, I wanted to use it on some other projects as well, so bringing
it up-to-date with modern web protocols seemed like a good idea.

### Current Project Status:
The _holy grail_ of MyCHIPs is a network implementation of the lift protocol introduced
in [this article](http://gotchoices.org/mychips/coupon.html) and explained in some more detail 
in [this article](http://gotchoices.org/mychips/acdc.html).  Unfortunately, that part is
not done yet.

However, I _have_ completed a functional framework which includes the following:
- Backend PostgreSQL database
  - Database authoring/modification tool
  - Data dictionary, including multi-language support
  - Basic schema to support many users per instance, multiple admins
  - Group/permission structures
- Multi-function Javascript server
  - Peer-to-peer process
  - Administrator server
  - User server (skeleton)
  - Agent-based modeling process (skeleton)
- Frontend GUI framework
  - Vue-based Single Page Applications for administration
  - Vue-based Single Page Applications for user access (skeleton)
  - Network visualization tool
  - Table previewer
  - Record editor
  - Parametric search tool
  - Support for reports, actions, other control-layer functions

If you are interested in participating, clone this repo and follow the instructions
in the [Developer Instructions](doc/Development).  You should be able to get a
simple demo network running and visualize it in the administrator console.

### Project Roadmap:
- ***Done:** Background: http://gotchoices.org/mychips/beginner.html **(Done)**
- ***Done:** Functional description: http://gotchoices.org/mychips/replace.html **(Done)**
- ***Done:** Basic architecture: http://gotchoices.org/mychips/software.html **(Done)**
- Reference server implementation **(In progress)**
  - Database schema management tool **(Done)**
  - Database GUI access tool **(Done)**
  - Tally/Chit exchange protocol **(Done)**
  - Basic user/peer/tally schema **(Done)**
  - Develop agent-based modeling tool **(In process)**
  - Develop lift algorithm
  - Develop contract editing, publishing, rendering, validation
  - Develop simple Wylib-based user SPA
  - Harden Database (implement users, groups, permissions, logins)
  - Harden Wylib/Wyseman (user validation)
  - Harden network communication (tickets, key exchange, noise-protocol)
- Early adopter testing (sandbox trading network)
- Rollout!
- Develop dedicated mobile user app

### Talent needs:
- Background: SSL/TLS, private/public key encryption
- Background: General Internet security
- Understand: Internet protocols
- Background: peer-to-peer networking
- Background: C++, server coding
- Background: Mobile app development
- Understand: accounting
- Understand: economics
- Understand: contract law

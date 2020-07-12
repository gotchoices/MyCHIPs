# MyCHIPs
MyCHIPs is an open-source network for implementing a novel kind of digital money based on private credit.

This is *not* a Bitcoin/blockchain derivative, but rather it seeks to address
several notorious problems with those technologies, most notably: it is fully decentralized and infinitely scalabile.

Briefly, if blockchain-based coins can be thought of as a crypto-stock or crypto-equity, a digital CHIP can be characterized as a crypto-bond.
Either one _can_ be used as money, or a medium of exchange.
However, a system based on private credit is more resilient to such forces as speculation, volatility, inflation, and deflation.
So it is a better solution when considering these three purposes of money:

    - a medium of exchange,
    - a store of value, and 
    - a measure of value.

For more in-depth information, please visit [this site.](http://gotchoices.org/mychips/intro.html)

### Getting Started:
To try out the software, follow the [Developer Instructions](doc/Development).

### Project Background:
In 2017, I posted this as an empty project on [github](http://github.com/gotchoices/mychips) hoping to attract a team of participants.
But there was not much traffic, and less interest.
Nearly everyone interested in monetary reform seemed to now be chasing after big returns in Blockchain money.
So I began programming the project myself.

Initially, this involved reviving some old tools I have successfully used on other projects in the past:
Specifically, [Wyseman](http://github.com/gotchoices/wyseman) and
[Wyselib](http://github.com/gotchoices/wyselib) for deployment of a backend database, and
[Wylib](http://github.com/gotchoices/wylib) for a frontend GUI.

While Wylib is not the solution for an eventual user interface, it has been what I needed for an administrative console during development.
And it can suffice for a crude user SPA until a dedicated mobile app can be built.

I have kept the source closed for some time while I tried to work out an algorithm for performing a distributed credit lift.
It also took me a while to come up with a licensing mechanism I would be comfortable with.
I wanted MyCHIPs to be free for everyone to use, but only if they will use it in honest trade as it was intended.

### Current Project Status:
The _holy grail_ of MyCHIPs has been a network implementation of the lift protocol introduced
in [this article](http://gotchoices.org/mychips/coupon.html) and explained in some more detail 
in [this article](http://gotchoices.org/mychips/acdc.html).

As of March, 2020, the software is successfully computing and performing fully distributed lifts in a simulated network.
I consider this a "preliminary proof of concept" and so am ready to release this code subject to the attched LICENSE.
It needs a lot more work to be production ready, but maybe more people will want to take a look now that there is actually something to see and test.

To kick off that process, I commissioned a study by [DSR Corporation](https://en.dsr-corporation.com/) to analyze the lift alorithm as proposed in the documentation and partially implemented in the software.
As expected, they uncovered several issues that need improvement before the system can be expected to perform in production.
Their work and results are included under the test/analysis directory.

In response to that study, I have created a file doc/Safety, my attempt to resolve the issues uncovered by the DSR study.
This represents the current state of the project.

### Milestones Completed so Far

- Backend PostgreSQL database
  - Database authoring/modification tool
  - Data dictionary, including multi-language support
  - Basic schema to support many users per instance
  - User/group/permission structures
  - Future capability for full ERP integration
  - CRUD+A API: CReate, Update, Delete + Actions/reports
- Multi-function Javascript server
  - Peer-to-peer process
  - Administrator server
  - User access to control layer
- Frontend GUI framework
  - Vue-based Single Page Applications for administration
  - Vue-based Single Page Applications for user access (demonstration only)
  - Network visualization tool
  - Table previewer
  - Record editor
  - Parametric search tool
  - Support for actions/reports other control-layer functions
  - Support for editing/viewing tally contracts
- Simulations
  - Agent-based modeling simulation process (very basic)
  - Local simulation engine (single host)
  - Network based simulation engine (multiple sites)
  - Docker based simulation engine (N sites)
  - Command line UI to create/analyze simulated data sets
- Model algorithm
  - Users can negotiate tallies with each other
  - Users can exchange chits (credit pledges) with each other
  - Sites can discover possible lift pathways through the network, with no central authority
  - Can (currently manually) initiate circular and linear lifts through the network
  - Chit transactions are stored in hash-chain list
  - Consensus algorithm between stock and foil
- Test algorithm (DSR Study)

If you are interested in participating, clone this repo and follow the instructions in the [Developer Instructions](doc/Development).
You should be able to get a simulated network running and visualize credit lifts in the administrator console.
Then review the work and results in the DSR study and see if you can help us move the project forward to deployment.

There is a project roadmap in the TODO file.

### Talent needs:
- Background: Distributed asynchronous network consensus protocols
- Background: SSL/TLS, private/public key encryption
- Background: General Internet security
- Understand: Internet protocols
- Background: peer-to-peer networking
- Background: JavaScript coding
- Background: SQL, PLPGSQL coding
- Background: Mobile app development
- Understand: accounting
- Understand: economics
- Understand: contract law

# MyCHIPs
MyCHIPs is an open-source network protocol for implementing a novel kind of digital money based on private credit and quantified in units of [CHIPs](http://gotchoices.org/mychips/definition.html):

The CHIP Symbol: <img src="doc/figures/chip.svg" alt="A CHIP" height="30"/>

This is *not* a Bitcoin/blockchain derivative, but rather a whole new (and yet [very old](https://www.bbc.com/news/business-40189959)) approach that solves several notorious problems with public blockchain systems.
Most notably, it is more [fully distributed](https://blockchainengineer.com/centralized-vs-decentralized-vs-distributed-network/) and infinitely scalable.

[![A Tiny CHIP Network](http://gotchoices.org/figures/money_ac.svg)](http://gotchoices.org/mychips/acdc.html "Click to see/run a decentralized private credit model")

If blockchain-based coins can be thought of as a crypto-stock or crypto-equity, a digital CHIP would be more like a *crypto-bond*.
Either one _can_ be used as money, or a medium of exchange.
However, a system based on private credit is more resilient to things like speculation, volatility, corruption, inflation, and deflation.
So it is a [better solution](http://gotchoices.org/mychips/bitcoin.html) when considering these three closely related purposes of money:

    - a medium of exchange,
    - a store of value, and 
    - a measure of value.

For introductory information on the algorithm, check out the [MyCHIPs Papers.](http://gotchoices.org/mychips/intro.html)

### Getting Started:
General documentation is found [here](doc/README.md).

To try out the software, jump in [here](doc/use-start.md).

At the current development state, you can launch a configurable number of server processes, as well as a network simulator to create bot users that will begin trading with each other.
There is also a rudimentary admin console that allows you to browse the database, generate user connection tokens, and peruse trading contracts.

### Project Background:
In 2017, I posted this as an empty project hoping to attract a team of participants.
But there was not much traffic, and less interest.
Nearly everyone interested in monetary reform seemed to now be chasing after big returns in Blockchain money.
So I began programming the project myself.

Initially, this involved reviving some old tools I have successfully used on other projects in the past:
Specifically, [Wyseman](http://github.com/gotchoices/wyseman) and
[Wyselib](http://github.com/gotchoices/wyselib) for deployment of a backend database, and
[Wylib](http://github.com/gotchoices/wylib) for a frontend GUI.

While Wylib is not the solution for an eventual user interface, it has been what I needed for an administrative console during development.
And it can suffice for a crude user SPA until a dedicated mobile app can be built.
As of Spring 2021, the BYU Capstone project produced a [prototype app](app/README.md) authored in Flutter/Dart.
Unfortunately the websocket interface is not yet finished so it does not yet talk to the MyCHIPs server.

I originally kept the source closed for some time while I tried to work out an algorithm for performing a distributed lift (the credit clearing function that makes the system work).
It also took me a while to figure out a contract and licensing structure I felt would make the system robust and resilient to attack.
I want MyCHIPs to be free for everyone to use, but only if they will use it in good-faith commerce and trade as it is intended.

### Current Project Status:
The _holy grail_ of MyCHIPs has been a network implementation of the lift protocol introduced in an intuitive way
in [this article](http://gotchoices.org/mychips/coupon.html) and explained in some more technical detail 
in [this article](http://gotchoices.org/mychips/acdc.html).

As of March, 2020, the software is successfully discovering, computing and performing fully distributed lifts in a simulated network.
I consider this as a "preliminary proof of concept" and so am ready to release this code subject to the attched [LICENSE](LICENSE).
It will need a lot more work to become production ready, but maybe this provides enough of a testing platform that others will be more willing to help make that happen.

To kick off the public release of the source code, I commissioned a study by [DSR Corporation](https://en.dsr-corporation.com/) to analyze the lift alorithm as proposed in the documentation and partially implemented in the software.
As expected, they uncovered several issues that need improvement before the system can be expected to perform in a fault-tolerant way.
Their work and results are summarized [here](test/analysis/dsr/phase-1/results.md).

In response to that study, I created an [outline](doc/old-safety.md) of how the algorithm might best be improved to resolve the issues uncovered by the DSR study.
Now there is work being done at [BYU](www.byu.edu) to both validate the original DSR results, and evaluate proposed solutions.
Early results would indicate that the [improved protocol](doc/learn-protocol.md) is now reasonably safe and live.

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
  - Prototype Flutter/Dart app
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
- Test original algorithm (DSR Study)
- Improved algorithm

Want to help out?  Clone this repo and follow the [instructions](sim-docker.md)
to get a simulated network running and visualize credit lifts in the administrator console.

There is a current project roadmap in the [TODO file](TODO).
[Let us know](http://gotchoices.org/contact.html) how you would like to participate!

### Talent Needs:
- Distributed asynchronous network consensus protocols (TLA+, SPIN)
- SSL/TLS, private/public key encryption
- General Internet security
- Internet protocols
- Peer-to-peer networking
- JavaScript/Node coding
- SQL, PLPGSQL coding
- Mobile app development
- Accounting
- Economics
- Contract law

### Other Interesting Projects/Resources:
- [Offset Credit](http://offsetcredit.org)
- [Trustlines](http://trustlines.network)
- [Open Credit Network](https://opencredit.network/)
- [Credit Commons](http://www.creditcommons.net)
- [The End of Money](https://www.amazon.com/End-Money-Future-Civilization/dp/1603580786)
- [Life After Google](https://www.amazon.com/Life-After-Google-Blockchain-Economy/dp/1621575764)

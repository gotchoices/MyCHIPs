## Learning MyCHIPs

### A Complex Problem
One of the first comments I often get after a code review is: "Wow, that is 
pretty complicated!"  Yes, there are a lot of moving parts in the algorithm.
But I think it is necessary for what we are trying to achieve.

Most any developer can visualize how to set up a private money system.  Just
make a big ledger and start recording transactions:  Bob sent Mary 3 units.
Then Dave sent Joe 7 units.  Put a nice UI on it so everyone can see how many
units they have, and you're all done.  Right?

Well, there a few big problems with this.

First, who gets to run the ledger?  You?  Government?  A bank?  That is the
whole problem with centralization--the question of authority.  And once you
pick someone to be in charge, that invariably leads to the potential for
fraud and corruption.

Next problem is, how do you get things started?  In other words, how does Bob
get his initial units so he has something to send to Mary?  One instinctive
solution is to begin by giving everyone a "starting supply."  Enter 1000 units
on the ledger for everyone and let them go from there.

First problem with this is:  Who are you to be giving out money?  Does that
imply that money can be made out of nothing (a common fallacy)?  It turns out,
money that can be given out for free doesn't end up being very good money.
And just because you are the central authority (keeper of the ledger) doesn't
mean you have money to award in the first place.

This problem can also be thought of as the money supply dilemma.  Who controls
the amount of money in the system?  And are there consequences to making more
or less of the stuff (inflation, for example).

Next problem is authenticity.  We commonly think of money as a thing that
allows two strangers, who have no preexisting relationship of trust, to engage
in a buy-sell transaction.  But this assumes the seller has some way to verify
that the money being given in consideration of the sale is genuine and real.

And when the money is digital, we have a double-spending dilemma.  How can one
be sure a digital token hasn't already been given to someone else, or many
someone elses?

These problems have been addressed in various ways by blockchain based money
but those systems are not without their own set of problems.  Most notably, 
they are very difficult to scale up to real-world use.

MyCHIPs takes a different approach from a public ledger.  The result is indeed
a bit complicated.  But it has some very desirable benefits.

So to be most effective as a developer, you should try to un-learn some ideas
about how money has to work that may be burned very deeply into your psyche.

### Money as Credit
The first thing to unlearn is that money has to be a commodity, an equity--a
thing that can be possessed (i.e. gold, silver, Bitcoin, etc.).  This is one of 
the reasons the "money supply" is such a difficult notion to grasp.  Because we 
think it is a thing, rather than just an abstraction (a promise) meant to 
represent a real thing, or the delivery of a real thing at some point in the
future.

In our ledger example above, it was easy to think about moving things (units)
around.  We just need the notion of ownership (equity) of things (units).  And
then we start making entries to keep track of who owns each unique thing.  As
long as no one (in authority or not) manages to create unauthorized (counterfeit) 
units, everything should work just fine.  But these problems of
authority, and money supply have proven over the last century to be too big to
handle--even for a large and powerful government.

Even the iconic Austrian economist Mises recognized that, in addition to what
he terms "real money" (gold, silver or similar commodities), there can be such
a thing as "money substitutes."  Credit money is one such substitute.  In fact,
nearly all money in use today is credit money.

In the MyCHIPs lexicon, we will often refer to credit money as simply "money." 
And what Mises called money, we may call "commodity money" for clarity.

Credit money can seem scary to some.  But it actually has some very desirable
qualities.  It is very egalitarian.  Commodity money is hard for anyone to
create.  You might have to discover a gold mine, or buy lots of servers to mine
Bitcoins.  But credit money can be created privately between any two willing
parties.  So anyone can create it.  And it can come into existence just as it 
is needed for the necessary transactions.

This solves the problem of how Bob pays Mary.  Everyone starts out at zero and
Bob just pays Mary.  Easy as that.  Bob's money goes negative and Mary's goes
positive.  It is a false assumption that the total, net money supply has to be
a positive number.  In fact, the basic rules of accounting tell us it must be 
zero.

Another way to explain this is in terms of physics.  We know that magnets
exist as "dipoles."  This means there is always a North pole for every South
pole.  It is doubtful whether magnetic "monopoles" even exist in nature.  But
we are all familiar with the dipolar nature of magnets.

And you can take a non-magnetic piece of steel and turn it into a North magnet
on one end--just as long as you are willing to have a South magnet show up on
the opposite end.

This is the true reality behind "creating money out of nothing."  Credit money
can be created out of nothing as long as you create a credit for every debit.
Just keep it in balance.

You can more easily think of commodity money as a monopole (even though that 
notion may not be entirely true either).  It is easier to see how the total 
gold supply could be a larger or smaller, but still positive number.  It is 
pretty hard to imagine having "negative gold."  Maybe you could owe some gold 
to someone.  But that's really what we're talking about with credit money.

So that's it.  We just need our ledger system to handle positive and negative
amounts, always making sure the net of all entries is zero, and we've solved 
the money supply problem.

### Decentralization
Now to the bigger problem relating to authority and trust.

Blockchain is said to be a decentralized system, and in many ways it is.  But
in addition to being based on a commodity model (as opposed to credit), all
tokens (monopoles) must emanate from a single algorithm.  In other words, there
are a finite number of possible tokens, and they are all distinctly identifyable
within a universe (coin type) of named money (Bitcoin, Litecoin, etc.).

The database that holds the ledger is kept in a pretty decentralized way.
And the authority to decide what transactions are entered is also decentralized.
But there is still only a single "correct" version of the ledger (excluding the
notion of forks and new, different coins).  Everyone that keeps the ledger has
to ultimately agree on the data to be considered valid.

In other words, it is one ledger--just decentralized in the way it is stored and
composed.

The remaining centralized nature of the blockchain is ultimately its achilles
heel.  This is often called the scalability problem.  Since there is really
only one ledger, transactions must compete for the limited bandwidth to get
into a block on the ledger.  This means, as more people try to use it, the cost
per transaction rises until it becomes prohibitively high.  Yes, there are
mechanisms available to mitigate this problem.  But in the end, any single coin
will face the problem of scaling.

These problems really relate mostly to commodity money.  Once we make the jump
to credit money, the opportunity for infinite scaling opens up wide.
With this comes the possibility for zero (or near zero) transaction costs.
But we have to understand what a fully decentralized 
(or [fully distributed](https://medium.com/nakamo-to/whats-the-difference-between-decentralized-and-distributed-1b8de5e7f5a4))
system would look like.
How can you track transactions in millions of distributed ledgers and still assure no one is cheating?

The answer lies in the nature of credit money as a dipole.  In the case of
the money Bob gave Mary, only Bob's ledger and Mary's ledger need to keep track 
of that transaction.  No one else's system need be encumbered with that data.  
As long as Bob and Mary agree, that is enough.

But that introduces a huge potential trust problem.  How do I do business with
people I don't trust?  This is why commodity money has such an appeal for most
advocates of monetary reform.

This is where the MyCHIPs lift algorithm shines.  It allows us to:

- Establish relationships with just a few other entities we already trust;
- Secure those relationships with binding contracts;
- Pass value through the network to entities with whom we do not share a direct 
  connection of trust.

### Maintaining Discipline
As one works on this project, it can be difficult to maintain these principles
and concepts firmly in mind, as necessary to achieve a fully distributed system.

For example, DNS itself has become a centralized system.  It started out quite
decentralized.  But as security became more important, it quickly became 
necessary to prevent people from spoofing a domain name.  So SSL and site
certificates were introduced to make sure the website we connect to is really
the one we intended.  This works pretty well as long as you trust the issuer of 
the toplevel certificate hard-coded into your browser.  But like nearly all
forms of centralization, it creates (in the best case) a monopoly or (in the
worst case) potential for corruption and abuse.

MyCHIPs hopes to avoid as much centralization as possible:  No central 
clearinghouse for transactions, no central database for ID's, and not even a 
central address or port for meeting other potential partners.

In its place, we expect people to meet in the real world, agree on trading 
terms, and then exchange trusted data in a strictly peer-to-peer way.  Rather 
than creating a central trading depot, we want to create a billion separate and 
secure connections--a billion separate and secure ledgers.  Then trusted 
partners can trade directly over these private and intimate connections.
Strangers can trade indirectly by rippling value through the network--but only 
if they are trustworthy enough to maintain their own local connections of 
trust.

<br>[Next - Support Libraries](work-hacking.md)
<br>[Back to Index](README.md#contents)

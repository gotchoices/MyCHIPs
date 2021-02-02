##MyCHIPs User Interface

###Visual Balance Sheet
It is a pretty obvious goal of MyCHIPs to create a dependable, alternative 
medium of exchange.  A less obvious goal is to build a diverse web of trusted
links of interdependency throughout society in order to make the world a more 
peaceful and friendly place to live in.

In order to accomplish these goals, the end-user interface must be simple
enough for everyone to use and understand.  It would be an added bonus if the
interface would imbue the user with deeper insights into:
  - The [true nature](http://gotchoices.org/mychips/value.html) of money/value
  - Sustainable and dependable savings strategies (Balance Sheet)
  - Healthy balance of productivity versus expenses (P&E)

Many people approach money management solely from the standpoint of meeting
their monthly expenses (P&E).  They produce what they need to pay the bills.
If there is extra left over, it gets spent on luxuries.  If there is not
enough, they may go without or try to get a raise or a better job.

This approach leaves many very close to the edge.  Some people live only one 
paycheck away from financial disaster.

A more healthy approach is to focus on the Balance Sheet, an indication of 
one's net worth, which is derived as the difference between one's assets and 
liabilities.  When people focus on increasing their net worth, the natural
outcome is to produce more than you consume.

Like the P&E approach, this assures there is enough to cover expenses each 
month.  But it also encourages you to save a little each month.  That is the
only way to get the balance sheet to grow.

Since most people are not used to reading a balance sheet, it would be helpful
to have a very intuitive graphical way of displaying net worth--something that
could be understood with a glance and that would encourage people to behave in
a way that is in their best financial interest.

This "Visual Balance Sheet" ([prototyped here](../test/visbs/index.html))
is intended to quantify several important aspects of one's balance sheet into 
a graphical object that is interesting to look at and easy to understand.

Quantities to model:
  - Total tally assets (stocks and debit-balance foils)
  - Total tally liabilities (foils and credit-balance stocks)
  - Number of tallies
  - Aggregate Magnitude (assets + liabilities)
  - Net Worth

Proposed Graph Dimensions:
  - Annular pie graph, relative size of slices
  - Hue of slices (asset/liability)
  - Shade of slices (different assets or liabilities)
  - Relative size and color of center core (net worth)

###Some Original Design Concepts (from 2017)
In addition to managing connections with other peer servers, a MyCHIPs server 
must manage connections with its own set of users.

It would be ideal if users could connect to their server in an entirely
different way than other peers do.  For example, the identity (or at least the
address and port) of my server will become known to one's partners as soon as
tallies are established with them.  It seems less than ideal if they can then 
use that information as the first step to try to hack into the user's account.

It would be perfectly feasible to accept user connections only on a different
port and even a completely different IP number.  Ideally, this endpoint would
be known only to the user who uses it.

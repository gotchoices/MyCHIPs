# Defining a CHIP
Jan 2022

## Project Background:
MyCHIPs creates a platform for transmitting value through a distributed network
of privately interconnected peers.
This is accomplished by way of the [lift algorithm](learn-lift.md).
In order for lifts to function effectively, the system needs a way to quantify the
units of value being exchanged at each [node](learn-node.md).

MyCHIPs uses the unit of CHIPs as described in the book
[Got Choices](http://gotchoices.org/book/chips.html) and defined in more detail
[here](http://gotchoices.org/mychips/definition.html).

Defining a perfectly objective unit of value is difficult--maybe impossible--since 
the idea of value is itself inherently relative.

For example, when we ask "how much is a bushel of corn worth," we are really asking how much of
some other commodity we may be expected to trade for it.
Perhaps that corn is equivalent to a gallon of milk, or an hour of work, or some needed transportation.

Historically, this problem has been mitigated by governments providing a standard unit of
measure for all other values to be measured against.
This can work well enough--until someone starts starts manipulating the monetary standard for their own interests.

The CHIP is intended to define a unit of value that is *practially objective*--not perfectly so,
but objective enough to work for it's intended purpose--and to function outside the influence of centralized actors.

The CHIP standard is backed by the commodity most everyone has an ongoing supply of: human labor.

This has some distinct advantages but it also has some distinct challenges:
For example, labor may seem much more valuable in a highly prosperous economy (like the US) as compared to one less developed (like India).
Why is this exactly?

Some of the difference can be explained by the cost of living in the two different countries.
But that really is a bit of a circular argument isn't it?

Other forces also play a part.
For example, people may choose to live at different standards of living in various cultures.
And border restrictions can create artificial barriers between markets, preventing equlibrium that would otherwise develop between them.

Most cost/value differences can be explained in terms of supply and demand.
How many people are available to fill a particular position?
And how many jobs are available for those looking for work?

## Objectives:
The goal of this project is to define a unit of measure (the CHIP) whose value transcends borders
and cultures.
It is a theoretical value based on one hour of standardized, normalized human labor.

By *standardized* we mean to define what general level of proficiency are possessed by the person providing that labor.
By *normalized* we mean to factor out external forces (such as imbalances of supply and demand) that cause the reference
productivity to be valued differently across differing economies.

For example, variances are likely caused by:
- Supply of labor
- Demand for labor
- Differing levels of skill, strength, talent, or education
- Differing access to labor saving capital (tools, technology, machinery, equipment)

## Strategy:
- Hypothesize what factors are responsible for variances in differing economies.
- Compare to the current CHIP definition and propose updates/modifications to that definition where necessary.
- Attempt to quantify the mathematical effect those factors have on wages and costs.
- Create a normalization function that allows conversion of labor costs between economies.
- Hypothesize samples of market data that can be taken from an economy to derive factor values.
- Provide a mathematical model for the collection and application of normalization data.

## Outcomes:
- A programmer can create a system to gather market data from market indexes published on the Internet.
- By applying the mathematical model to the sample data, it will be possible to
  publish the current value of a CHIP, expressed in units of any existing national currency.
- Currencies based on fractional reserve banking systems are expected to experience
  ongoing inflation.
- The standardized, normalized measure of value should remain constant in terms of its relationship to human labor.
- As technology increases, it is expected that the production of most commodities will become more efficient over time (as expressed in the amount of standardized labor required to produce them).
- In a technologically advancing culture, the cost of most commodities (not subject to supply limitations) is expected to fall over time.
- The standard of living should gradually increase (absent war and other forms of capital destruction).
- The CHIP can supply a stable reference value by which to measure all other change.

## Technical Considerations:
This project has two phases:
- Creation of the economic model
- Writing a program to sample economic data and publish ongoing results

## A Suggested Approach:
It is fairly straightforward to construct a table of
[commodities futures prices](https://www.agweb.com/markets/futures) as follows:

| Commodity | Unit | USD | Euro | Other |
| :--- | :--- | ---: | ---: | ---: |
| Corn | Bushel | 7 | 7.70 | a |
| Wheat | Bushel | 10 | 11 | b |
| Hogs | Pound | 1 | 1.1 | c |
| Crude | Barrel | 100 | 110 | d |

An obvious question arises: What kind of corn?
Is corn with a higher calorie value worth more than other corn.
Are the ears big and healthy or small and wormy?

To answer these questions, we have to drill deeper by clicking on the link for the price in question.
Futures prices are based on a particular *contract*--for example, a corn contract 
[CBOT](https://www.agweb.com/markets/futures?module=futureDetail&symbol=ZCK22&override=&region=)
issued by the Chigaco Board of Trade.
This is a contract actually issued to farmers by which they can sell their corn in advance of harvest at a predictable price.

Now futures prices are not exactly an indication of a market in equilibrium (balanced supply and demand).
But this table will serve as a starting point before going on to the exercise of normalizing the data for that distortion.

Next question is, could we add labor to the table?

| Commodity | Unit | USD | Euro | Other |
| :--- | :--- | ---: | ---: | ---: |
| Corn | Bushel | 7 | 7.70 | a |
| Wheat | Bushel | 10 | 11 | b |
| Hogs | Pound | 1 | 1.1 | c |
| Crude | Barrel | 100 | 110 | d |
| Labor | CHIP | 10 | 11 | 3 |

First instinct says that would be very hard.
After all, what kind of labor?
Everyone's labor is worth something different right?

Yes, it is harder than valuing a bushel of corn.
There are a lot more variabilities to work out.
But we should be able to get a pretty good estimate by 
consulting market data about current labor costs and trying 
to factor those costs in comparison to the standard CHIP definition.

Next question is, why are commodities bound to rows and currencies bound to columns?
For example, couldn't we price all our commodities in terms of wheat as follows:

| Commodity | Unit | USD | Euro | Wheat |
| :--- | :--- | ---: | ---: | ---: |
| Corn | Bushel | 7 | 7.70 | 0.7 |
| Wheat | Bushel | 10 | 11 | 1 |
| Hogs | Pound | 1 | 1.1 | 0.1 |
| Crude | Barrel | 100 | 110 | 10 |
| Labor | CHIP | 10 | 11 | 1 |

Likewise, there's no reason we couldn't put currencies on their own row, and move
Labor CHIPs to a column:

| Commodity | Unit | USD | Euro | Wheat | CHIP |
| :--- | :--- | ---: | ---: | ---: | ---: |
| Corn | Bushel | 7 | 7.70 | 0.7 | 0.7 |
| Wheat | Bushel | 10 | 11 | 1 | 1 |
| Hogs | Pound | 1 | 1.1 | 0.1 | 0.1 |
| Crude | Barrel | 100 | 110 | 10 | 10 |
| Labor | CHIP | 10 | 11 | 1 | 1 |
| USD | Dollar | 1 | 1.1 | 0.1 | 0.1 |

To get this far is a big accomplishment.  It will mean locating market data about
current (or expected) labor costs, measured against the standard CHIP definition.

The next step is to build normalization functions to remove the speculative nature of
- futures pricing; and
- market distortions due to border restrictions

Some questions for consideration:
- How can one tell when the supply and demand for any given commodity is in equilibrium?
- Can we quantify how much this affects current prices?
- Or do we just reject outlying data and rely on data coming from times/places where equilibrium is achieved (or crossed)?
- How do prices normalize across borders with fairly open trade policies?
- How are prices constrained across more closed borders?
- How much is paid in the US for unskilled labor?
  - How much when the worker is a US citizen?
  - How much when the worker is an undocumented foreigner?
  - How much when the work is a citizen of India or Pakistan working over the Internet?
- How much is paid in India for unskilled labor?
  - Are there jobs in India that are difficult, but just possible to fill?
  - How much is paid for that work?
  - How much when the work is a citizen of India or Pakistan working over the Internet?

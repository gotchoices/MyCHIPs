# Computing the Value of a CHIP
Jun 2022

## Project Background:
[MyCHIPs](http://gotchoices.org/mychips) creates a platform for transmitting value through 
a distributed network of privately interconnected peers.
This is accomplished by way of the [lift algorithm](learn-lift.md).
In order for lifts to function effectively, the system needs a way to quantify the
units of value being exchanged at each [node](learn-node.md).

MyCHIPs uses the monetary unit of CHIPs as described in the book
[Got Choices](http://gotchoices.org/book/chips.html) and defined in more detail
[here](http://gotchoices.org/mychips/definition.html).

Defining a perfectly objective unit of value is difficult--probably impossible--since 
the idea of value is itself inherently relative.

For example, when we ask "how much is a bushel of corn worth," we are really asking how much of
some other commodity we may be expected to trade for it.
Perhaps that corn is equivalent to a gallon of milk, or an hour of work, or some needed transportation.
More commonly, we express the value in terms of some government-issued currency.

The CHIP is intended to define a unit of value that is independent of government or other centralized controls.
It is designed to be *practically objective*--not perfectly so,
but objective enough to work for it's intended purpose.

In order to achieve maximum independence and stability, 
a CHIP is measured against the commodity most everyone has an ongoing supply of: human labor.
This has some distinct advantages but it also has some challenges:
- First, the labor of one person is seldom, if ever, equal to the labor of another.
- Furthermore, labor costs vary greatly across different economies (compare the US
  to India, for example).

The economic [Law of One Price](https://en.wikipedia.org/wiki/Law_of_one_price) asserts
that in the absense of trade frictions such as transportation, borders and regulations,
the price of any given commodity should eventually converge toward a single value 
regardless of location.

So to determine a useful standard of value based on labor, we need a way to
express how valuable some nominal standard of labor is, absent such frictions.

## Objectives:
The goal of this project is to define a unit of measure (the CHIP) whose value transcends borders and cultures.
It is a theoretical value based on one hour of *nominal work* we will
refer to as standardized, normalized human labor.
- By *standardized* we mean to define what general level of utility is provided by the person performing the labor.
- By *normalized* we mean to factor out frictions and distortions that cause the reference
productivity to be valued differently in different locations and markets.

In simple terms, the CHIP unit seeks to express how much value markets put, at any given
time,  on an hour of unskilled labor in a hypothetical condition of market equilibrium 
(supply = demand) and absent regulatory or other artificial distortions.

Distortions are likely to include:
- Unusually high or low supply of labor
- Resulting distortion in the demand for labor
- Differing levels of skill, strength, talent, and education
- Differing access to labor saving capital (tools, technology, machinery, equipment)

## Possible Strategies:
- Hypothesize/confirm what factors are responsible for variances in differing economies.
- Compare to the current [CHIP definition](http://gotchoices.org/mychips/definition.html) 
  and propose updates/modifications to that definition where necessary.
- Quantify the mathematical effect those factors have on wages and costs.
- Create a normalization function that allows conversion of labor costs between economies.
- Hypothesize samples of market data that can be taken from an economy to derive factor values.
- Provide a mathematical model for the collection and application of normalization data.
- Investigate the suitability of existing commodity indexes as a basis for CHIP calculation.
- Model capital equipment as an accumulation of past labor (i.e. the depreciating portion of the accumulated total of past labor inputs).
- Model more educated workers as an aggregate of the inputs:
  - Basic unskilled labor; and
  - Education and training, viewed as a kind of capital asset (which can be valued based on accumlation of other labor inputs as noted previously).

## Outcomes:
- Provide a working prototype that produces a quantified number, expressed in terms of a chosen traditional currency.
- This may be implemented in a spreadsheet, matlab or other such mechanism familiar to the researcher.
- From the prototype, a developer can create a computer program to gather market data from sources published on the Internet.
- By applying the mathematical model to the sample data, it will be possible to
  publish a web page showing a past and/or current value of a CHIP, expressed in units of any chosen existing national currency.

## Expected Results:
- Currencies based on fractional reserve banking systems are likely to experience ongoing inflation.
- The CHIP unit of value should remain constant in terms of its relationship to human labor.
- As technology increases, production of most (non-supply limited) commodities should become more efficient over time (as expressed in the amount of standardized labor required to produce them).
- In a technologically advancing culture, the cost of such is expected to fall over time.
- The standard of living should gradually increase (absent war, attrition and other forms of capital destruction).
- The CHIP can supply a stable reference value by which to measure all other change.

## Technical Considerations:
This project has two phases:
- Creation of the economic/mathematical model and prototype calculation engine,
- Writing a computer program to sample economic data, compute the index, publish past and current results in the form of a web page.

Researchers may prefer to engage on one or both phases as their expertise allows.

## One Possible Approach:
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

## Some Questions for Consideration:
- How can one tell when the supply and demand for any given commodity is in equilibrium?
- Can we quantify how much this affects current prices?
- Or do we just reject outlying data and rely on data coming from times/places where equilibrium is achieved (or crossed)?
- How do prices normalize across borders with fairly open trade policies?
- How are prices constrained across more closed borders?
- How much is paid in the US for unskilled labor?
  - How much when the worker is a US citizen?
  - How much when the worker is an undocumented foreigner?
  - How much when the work is delivered from India over the Internet?
- How much is paid in India for unskilled labor?
  - Are there jobs in India that are difficult, but just possible to fill (i.e near equilibrium)?
  - How much is paid for that work?
  - How much when the work is delivered from India over the Internet?

## Some Resources of Possible Interest:
- [The MyCHIPs Papers](http://gotchoices.org/mychips)
- [The CHIP Definition](http://gotchoices.org/mychips/definition.html)
- [Purchasing Power Parity](https://en.wikipedia.org/wiki/Purchasing_power_parity)
- [A Source for World Economic Data](https://www.theglobaleconomy.com)
- [The Rogers Commodity Index](https://en.wikipedia.org/wiki/Rogers_International_Commodity_Index)

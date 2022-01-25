# Defining a CHIP
Jan 2022

## Project Background:
MyCHIPs creates a platform for transmitting value through a distributed network
of privately interconnected peers.
In order to function effectively, the system needs a way to quantify the
units of value being sent.

MyCHIPs uses the unit of CHIPs as described in the book
[Got Choices](http://gotchoices.org/book/chips.html) and defined in more detail
[here](http://gotchoices.org/mychips/definition.html).

Defining a completely objective unit of value is difficult--maybe impossible--since 
the idea of value is itself inherently relative.

When we ask "how much is a bushel of corn worth," we are really asking how much of
some other commodity are we expected to trade for it.
Maybe that corn is worth five dollars, or 1 hours work, or some needed transportation.

Historically, this problem has been mitigated by governments providing a standard unit of
measure for all other value to be measured against.
This can work well enough--until someone starts debasing or otherwise manipulating the monetary standard.

The CHIP is intended to make a unit of value as objective as possible.
It does so by tying the standard to the commodity most everyone has an ongoing supply of: human labor.

But that can be tricky too.
Labor may seem to be much more valuable in a highly prosperous economy as compared to one less developed.
For example, labor in the United States might be much more expensive than labor in, for example, India.
But why?

Some of the difference can be factored out by considering the cost of living in the two
different countries.
But other forces also play a part.
For example, people may expect to live at a different standard of living in the various cultures.
And border restrictions create artificial barriers between the markets, preventing normalization that might otherwise occur between them.

Also, there may be many more people seeking employment in certain economies.
Or there may be fewer opportunities for gainful employment.

## Objectives:
The goal of this project is to define a unit of measure (the CHIP) whose value transends borders
and cultures.
It is a theoretical value based on one hour of standardized, normalized human labor.

By *standardized* we mean to define what general level of proficiency and capabilties are possessed by the person providing that labor.
By *normalized* we mean to factor out external forces that cause the reference
value to be perceived differently across different borders and cultures.

For example, variances may be caused by:
- Supply of labor
- Demand for labor
- Differing levels of skill, strength, talent, or education
- Differing access to labor saving capital

## Strategy:
- Hypothesize what factors are responsible for variances in differing economies.
- Compare to the current CHIP definition and propose updates/modifications to that definition where necessary.
- Attempt to quantify the mathematical effect those factors have on wages and costs.
- Create a normalization function that allows conversion of labor costs between economies.
- Hypothesize samples of market data that can be taken from an economy to derive factor values.
- Provide a mathematical model for the collection and application of normalization data.

## Outcomes:
- A programmer can create a system to gather market data from the Internet.
- By applying the mathematical model to the sample data, it will be possible to
  publish the current value of a CHIP, expressed in units of current national currencies.
- Currencies based on fractional reserve banking systems are expected to experience
  ongoing inflation.
- The standardized, normalized measure of value should remain constant in terms of its relationship to human labor.
- As technology increases, it is expected that the production of most commodities will become more efficient over time.
- In a technologically advancing culture, the cost of most commodities (not subject to supply limitations) is expected to fall over time.
- The standard of living should gradually increase.
- The CHIP can supply a stable reference value by which to measure all other change.

## Technical Considerations:
This project has two phases:
- Creation of the economic model
- Writing a program to sample economic data and publish ongoing results

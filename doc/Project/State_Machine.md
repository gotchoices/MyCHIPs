# MyCHIPs State Processing
July 2020

## Project Background:
The current MyCHIPs proof-of-concept release maintains state in a PostgreSQL
database.  This database is surrounded by one or more NodeJS server processes
which route traffic to/from administrators, users and peer systems.  This is 
shown in this [LibreOffice figure.](/doc/Scaling.png).

The originally released code was crafted according to a set of proposed state 
transitions documented [here](/doc/States.odg).  The protocol and state
machines evolved through an iterative process while trying to understand and
develop the process itself.  This is not ideal for the generation of clean
and efficient code.

Additionally, very little has been done in the way of unit testing.  Ideally
unit tests would be created first and then the code would be produced to match
a clearly crafted specification.  The algorithm was not initially understood 
well enough to follow this design pattern.

A [study](/test/analysis/dsr/phase-1/results.md) was recently commissioned to
study the proposed state flow--particularly as it relates to the distributed
lift protocol.  This study revealed several potential flaws in the protocol.

There is a parallel [project](/doc/projects/Lift_Protocol.md) to refine the
lift protocol to address the current flaws.  Subject to the results of that
project, it will be necessary to upgrade the current state transitioni logic
to implement the improved protococl specification.

## Objectives:
The goal of this project is to upgrade the current state control logic to
implement the improved protocol specification.  Messages received from users
and peers need to be interpreted, checked for form and content, and then sent
to the PostgreSQL control/model core so that state transitions can occur with
[ACID](https://en.wikipedia.org/wiki/ACID#:~:text=In%20computer%20science%2C%20ACID%20(atomicity,errors%2C%20power%20failures%2C%20etc.).

State machines exist for the generation and management of:
- Tallies
- Chits
- Route discovery
- Lift execution

A suite of unit tests should be created to test each possible case of state
transitions.  The production server should then be invoked against each test
case and these tests should be integrated into the current source tree.

## Outcomes:
- Evaluate the form and function of the existing state transition logic
- Plan/architect any code structure improvements
- Model state transition diagrams in test logic
- Write unit tests against state transition logic
- Implement code improvements to state transition logic
- Evaluate against unit tests
- Unit tests run under existing Node module structure (npm test)

## Technical Considerations:
Current limited unit tests are implemented in mocha.

New unit tests may use mocha or some other framework, but should integrate
properly with the existing tests.

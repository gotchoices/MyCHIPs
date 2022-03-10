# Agent 3 Simulation

The Agent 3 simulation extends the basic structure Agent 2 was built on and adds key features that result in more realistic spending patterns.

### Primary Goals

- Improve code readability for future developers (Completed)
  - Update variable names
  - Implement classes that adhere to the Single Responsibility Principle
  - Convert JavaScript to TypeScript
- Collect data from simulation that can later be analyzed
  - Add analytics table to WorldDB that records both server and world information
  - Export to single file
- Add configurable actions to simulation
  - Easily allow other developers to create their own actions
  - Actions (such as purchase a house, buy a car, or get a paycheck) can be configured with their frequency depending on the account type
- Perform credit lifts when criteria is met

## Structure Overview

\*Details on low-level implementation are provided in code as Javadoc comments

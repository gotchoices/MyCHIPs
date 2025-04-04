# MyCHIPs Chark Project Guide for Developers and AI agents

## General Principles
- Normalized code
  - reusable
  - consistent
  - single-responsibility, single point of change
- Solve problems the right way, don't kludge
- Program is functional, don't break it, do improvements in little, incremental steps
- Comments should add necessary information where function is not already obvious
- App was authored in javascript but it is a goal to gradually migrate to typescript
  if this can be done in a non-disruptive way
- Handle functions like cryptography, conversions centrally, consistently
- Standardize formats for dates, UUIDs, etc
- Systematize repetative tasks; examples: bin/tallylaunch, fastlane
- Use test-driven workflow when beneficial/optimal (non-UI?)

## User Experience
- Strive for an intuitive UI
- Minimize English/other written language, use expressive icons where possible
- Provide context helps for DB properties
- Handle errors gracefully with informative messages
- Support offline operations where possible

## Language Prompts
- Any language content must be included in and fetched from the backend data dictionary
- Don't hard-code English into the app (exception for debugging)

## Data and State Management
- Maintain single source of truth for data, model-view-controller
- Use Redux for global state
- UI relies on redux even when backend not available
- UI triggers requests to backend for data that may be needed or has changed
- Response updates redux, UI components will follow if they are visible
- UI objects not visible will still benefit from up-to-date data when they do become visible
- Backend can send unsolicited data, which will also be updated appropriately in redux

## Network Communication
- Re-connect as/when needed
- Stay connected until connection times out or app goes to sleep
- On reconnect, query for updates since last connection (migrate to this goal)

## Work Flow
- Create file for each new issue (see issues/README.md)
  - Describe work to be done: bugs, problems, goals, objectives
  - Discover root causes as necessary
  - Plan upgrade strategy
  - Evaluate effect on, compliance with, other code modules
  - Document in issue file detailed checklist of all relevant files,items,tasks
  - Do improvements in small, incremental stages
    - Build regression test (if applicable)
    - Implement incremental change
    - Test, adjust until working, clean, optimize
    - Update checklist, commit code
    - Iterate through checklist
  - Document possible future enhancements
  - Document other modules that may benefit from enhancements (new issues?)

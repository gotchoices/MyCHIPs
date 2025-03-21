# Optimizing Backend Communication via Wyseman API

**Status: IN PROGRESS** - Further optimization of the API process is needed

## Background
- Wyseman was originally developed as part of the WyattERP suite
  - It is designed on the model-view-controller paradigm
  - One of its features is to handle communication between a view and the control/model layers
  - The first views developed were based in a web browser
  - Communications are done over a websocket (not a lot of options in a web browser)
- This same interface has been adapted for use with the MyCHIPs react native mobile app
- Wylib has its own authentication mechanism primed with one-time connection token
  - Once connected, the client generates a key and shares the public version over the now-open channel
  - Subsequent connections are authorized by this key
- Communication happens by sending JSON packets over the socket
- Packets are also delimited by frame markers
- Communication is necessarily asynchronous as responses may not come back for some time (or in some edge cases, not at all)
- The backend contains substantially all authoritative data for the app
- The backend also contains data dictionary information such as table, view, column descriptions
- The backend also contains language (localization) data for a variety of languages
- The MyCHIPs app is responsible for maintaining its own view state but it must take care to remain
  in sync with the data state in the backend
- The backend also supplies various reports that can return results in a variety of formats (text, json, html, for example)
  - HTML reports can be integrated into the app by way of a webview to reduce dedicated native re-coding
- The websocket state is tracked by a connection status indicator on the screen (red, yellow or green)
- The protocol is characterized as CRUD+:
  - The 4 basic CRUD functions are accomplished via SQL encoded as JSON, targeted toward permissioned
    views with underlying tables that may have a great deal of control logic baked into triggers/functions
  - The '+' implies additional functionality because arbitrary stored functions and reports can also be called
- The Wyseman connection module client_ws is accessed via src/connect.js
- Message handling (in client_msg.js) is accessed via src/wyseman.js

## Current Issues
- The app does not deal optimally with wyseman API communication
- Sometimes, queries are sent off and we see a spinning wheel with no results and no timeout handling
- Sometimes, queries produce an error on the backend which is never recognized or displayed in the view
  - Example: When signing a payment chit, if the signature fails on the backend, there is
    no indication of this failure to the user
- The wyseman client_msg module does a fair amount of caching and may not be directly applicable
  in a system where Redux might serve a similar purpose

## Goals
- Connection should be made on demand and then remain open until interrupted by external means
- Support receiving unsolicited packets on an open connection (such as async updates/notifications from the database)
- Queries should have a unique id with an associated handler to be called when the data eventually returns
- Implement timeout handling for queries with proper user feedback when data is not returned
- Make the system tolerant of packets being returned multiple times (updating data each time)
- Properly report backend error conditions to the user
  - Eventually implement a persistent log of errors
- Ensure state changes are recorded correctly even for non-visible UI components
- Optimize bandwidth usage by minimizing unnecessary queries
- Consider querying for only recent changes on app launch and rely on asynchronous updates thereafter

## Questions to Resolve
- Should Redux store both view state (UI configuration) and data state (content)?
- Is wyseman's caching redundant with Redux state management?
- Is the current Redux implementation correct and optimal for our use case?
- How can we make the API interface more robust, dependable, and efficient?
- What flaws exist in the current code structure?
- What improvements can be made incrementally to allow testing as we go?

## Strategic Approach
1. **Diagnostic Phase**:
   - Add logging to trace the data flow when fetching user information
   - Identify exactly where and why data inconsistencies occur
   - Examine the interaction between Redux state and the Wyseman API

2. **Design Phase**:
   - Develop a more robust error handling and timeout mechanism
   - Create a more consistent pattern for API requests and response handling
   - Determine the optimal relationship between wyseman caching and Redux state

3. **Implementation Phase**:
   - Implement improved error handling and timeouts
   - Add better user feedback for API operations
   - Refactor the API communication layer incrementally

4. **Testing Phase**:
   - Test each incremental change to verify improvements
   - Ensure backward compatibility with existing features
   - Validate that all display issues are resolved

## Next Steps for API Communication
As we continue to improve the API communication layer, here are key areas to focus on:

1. **Standardized Error Handling**:
   - Implement a consistent approach to error handling across all API calls
   - Add proper user feedback for critical errors
   - Consider a centralized error logging and reporting system

2. **Request Timeout Management**:
   - Add timeout handling for all API requests
   - Implement retry logic for transient failures
   - Consider a circuit breaker pattern for persistent backend issues

3. **State Management Improvements**:
   - Better coordination between React Context and Redux state
   - Clear separation between UI state and data state
   - More robust hydration of state from persistent storage
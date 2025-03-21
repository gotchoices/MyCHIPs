# Optimizing Backend Communication via Wyseman API

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
- **Critical bug after RN 0.77 upgrade**:
  - The user's name and photo no longer display on the home page
  - On initial upgrade, the image and name were visible briefly upon app launch
    but disappeared within seconds (likely after receiving a response from the backend)
  - In subsequent app launches, the photo and name never appear at all, not even briefly
  - This suggests that previously cached data was being displayed momentarily, but the 
    communication with the backend is now failing to update the Redux store correctly

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
   - Identify exactly where and why the user photo/name are disappearing
   - Examine the interaction between Redux state and the Wyseman API

2. **Design Phase**:
   - Develop a more robust error handling and timeout mechanism
   - Create a more consistent pattern for API requests and response handling
   - Determine the optimal relationship between wyseman caching and Redux state

3. **Implementation Phase**:
   - Fix the immediate user photo/name display issue
   - Implement improved error handling and timeouts
   - Add better user feedback for API operations
   - Refactor the API communication layer incrementally

4. **Testing Phase**:
   - Test each incremental change to verify improvements
   - Ensure backward compatibility with existing features
   - Validate that the user photo/name display issue is resolved

## Progress Tracking
We'll use this section to document our steps, findings, and progress as we work through this issue:

1. Initial analysis of the code structure:
   - The websocket connection is managed in `src/components/SocketProvider.jsx`
   - User data is fetched via `query_user()` in `src/utils/user.js` 
   - The data is stored in Redux via the `currentUserSlice` reducer
   - The profile data (personal info including name) is in `profileSlice`
   - The avatar image is handled in the `avatarSlice`

2. Test Case Resolution:
   - We identified and fixed the issue with the user's name and photo not displaying on the home page
   - The root cause was in how React's dependency tracking worked when using Hermes (React Native 0.77's JavaScript engine)
   - When the Navigator component received user data through Redux, the useEffect that was supposed to fetch profile data wasn't triggering

### The Fix
We modified the Navigator component by:
1. Splitting the useEffect into two separate effects:
   - One specifically for user-related data fetching
   - One for general initialization tasks
2. Changing the dependency array to use the full `user` object instead of just `user_ent`:
   ```javascript
   // Before: This didn't reliably detect user changes in Hermes
   useEffect(() => {
     // Fetch user data...
   }, [wm, dispatch, user_ent, fetchAvatar]);
   
   // After: Split effects with improved dependency tracking
   useEffect(() => {
     if (user_ent && wm) {
       dispatch(fetchAvatar({ wm, user_ent }));
       dispatch(fetchPersonalAndCurrency({ wm, user_ent }));
     }
   }, [user, wm, dispatch]); // Using the full user object ensures proper detection
   
   useEffect(() => {
     // Other initialization tasks...
   }, [wm, dispatch]);
   ```

### Root Cause Analysis
The issue stemmed from differences in how Hermes (the JavaScript engine in RN 0.77) handles reference equality compared to the previous engine. 

- In the original code, we were using `user_ent` (a string derived from the user object) in the dependency array
- When the Redux state updated with a new user object, Hermes did not recognize that `user_ent` had changed
- By using the full `user` object in the dependency array, we ensure that React detects when the Redux state changes

This is a common issue when upgrading to newer JavaScript engines or React versions - subtle changes in reference comparison can break dependency tracking in useEffect hooks.

### Lessons Learned
1. For React/Redux applications, it's generally better to include the full state objects in useEffect dependency arrays rather than derived primitive values
2. When upgrading React Native versions (especially with engine changes like Hermes), watch for subtle changes in how React's dependency tracking works
3. Splitting useEffect hooks by responsibility makes them more reliable and easier to debug

### Additional Improvements
Beyond fixing the immediate issue with the user's name and photo, we made several additional improvements to the codebase:

1. **Improved Error Handling**:
   - Updated error handling in API calls to be more consistent
   - Changed handling of missing dependencies (like undefined `wm`) to use non-resolving promises
   - This prevents crashes but could be further improved with better user feedback

2. **Enhanced Code Documentation**:
   - Added clear JSDoc comments to key API functions in `src/services/profile.js`
   - Documented function parameters, return values, and behaviors
   - Improved readability and maintainability of the codebase

3. **Fixed Utility Functions**:
   - Enhanced `getIntegerValue` and `getDecimalValue` in `src/utils/user.js`
   - Added proper input validation and consistent return behavior
   - Fixed edge case handling for these frequently used functions

### Next Steps for API Communication
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

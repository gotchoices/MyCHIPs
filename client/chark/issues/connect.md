# Connection Ticket and Backend Connectivity Issues

*Last updated: April 5, 2025*

## Background

The MyCHIPs mobile application needs to connect securely to a backend service provider. This connection is established using a connection ticket mechanism where users receive a connection token from their provider. The app should reliably maintain this connection, properly handle token scanning and renewal, and guide users through the appropriate flow when no connection exists.

## Current Problems

1. **Intermittent Connectivity Loss**:
   - App sometimes loses connectivity with the backend after updates or app restarts
   - Problem is intermittent and may not appear for extended periods

2. **Connection Key Management**:
   - No current way to back up a connection key
   - No clear process for renewing keys when needed

3. **Scanner Integration Issues**:
   - When using the integrated scanner to read a connection token:
     - Connection is made immediately upon scan completion
     - Alert then appears asking if user wants to use the connection token
     - If user cancels, all is well
     - If user says OK, it attempts another connection with used token, causing failure

4. **First-Time User Experience**:
   - When app is launched for first time with no connection token:
     - App launches to empty home screen without guidance
     - No indication of what needs to be done (sign up with provider)
     - No language localization data (requires backend connection)
     - Redirect to https://mychips.org/nokey.html isn't reliable

5. **Service Provider Discovery**:
   - No single service provider for MyCHIPs
   - Users need to select a provider or run their own backend instance
   - No guidance on how to do this within the app

6. **Language Bootstrapping Challenge**:
   - Can't determine user's language before backend connection
   - Reliance on mychips.org for multilingual instructions isn't seamless

## Code Analysis Results

After examining the codebase, we've identified specific issues contributing to connection problems:

### ✅ Fixed Issues

1. **No First-Launch Detection** *(Fixed)*:
   - Problem: No specific logic to detect and handle first app launch scenario with no connection key
   - Solution: Added redirection to help page when no connection key exists in the keychain
   - Implementation: Modified `connectSocket()` to check for missing credentials and redirect to mychips.org/nokey.html

2. **Missing Tally Fetch After New Connection** *(Fixed)*:
   - Problem: When connecting with a new token to an account with existing tallies, the app showed an empty screen
   - Solution: Added automatic tally fetch after successful connection with a new token
   - Implementation: Created a wrapper callback in `connectSocket()` that fetches tallies only on successful new token connections

3. **Connection Key Reset Bug** *(Fixed - Data Loss Prevention)*:
   - Problem: In `src/screens/Scanner/index.jsx:169`, the app was calling `Keychain.resetGenericPassword()` on any connection error
   - This was deleting the previous valid connection key before confirming the new key works
   - Impact: If new connection failed for any reason, both old and new keys were lost
   - Solution: Removed the redundant key reset in the error handler, keeping it only in the successful path
   - Implementation: Modified the Scanner component's connection callback to preserve existing keys on error

4. **Reversed Connection Flow** *(Fixed - UX/Security Improvement)*:
   - Problem: In `src/screens/Scanner/index.jsx:56-62`, the app was connecting immediately with a new ticket if no current connection
   - Only if already connected would it show a confirmation dialog first
   - Impact: No user confirmation before making initial connections
   - Solution: Always show confirmation alert regardless of current connection state
   - Implementation: Modified both URL and JSON connection paths to always ask for confirmation
   
### Critical Issues (High Priority)

1. **Duplicate Deep Link Handlers** *(Critical - Race Condition)*:
   - Both `SocketProvider.jsx` (lines 31-43) and `Home/index.jsx` (lines 72-119) handle the same ticket URLs
   - No coordination between these handlers
   - Result: Potential race conditions or duplicate connection attempts

### Significant Issues (Medium Priority)

4. **Connection Key Storage Weakness** *(Security/Reliability Issue)*:
   - In `src/connect.js:42-52`, connection key is stored with minimal error handling
   - Unlike signing keys (`keychain-store.js`), connection keys lack robust storage and validation
   - Result: No recovery mechanism if storage fails

5. **No Connection Key Validation** *(Reliability Issue)*:
   - In `SocketProvider.jsx:155-164`, stored keys are used without validation
   - No checks for well-formed data before connection attempts
   - Result: Corrupt/malformed keys can cause crashes or connection failures

6. **Unconditional Navigation** *(UX Issue)*:
   - In `src/screens/Scanner/index.jsx:177`, navigation happens immediately on successful connection
   - User isn't notified about successful connection before redirection
   - Result: Abrupt navigation without context

### Possible Contributing Factors (Lower Priority)

7. **Navigation Configuration Limitations**:
   - `App.js:27-28` uses default `getStateFromPath` without customization
   - May not handle deep link parameters correctly in all cases

8. **Reconnection Strategy Limitations**:
   - Exponential backoff implementation in `SocketProvider.jsx` lacks maximum retry limit
   - No user notification about reconnection attempts

## Proposed Solutions (Prioritized)

### Phase 1: Fix Critical Bugs (Connection Key Preservation)

1. **Fix Connection Key Reset Bug**:
   ```javascript
   // In Scanner component, modify connect callback to preserve keys on error:
   connectSocket(
     {
       ticket,
     },
     (err, connected) => {
       if (err) {
         setIsConnecting(false);
         // REMOVE RESET: Keychain.resetGenericPassword(); 
         disconnectSocket();
         Alert.alert(err.message);
         setTimeout(() => setIsActive(true), 1000);
       } else if (connected) {
         // Only reset old key AFTER confirming new connection works
         setIsConnecting(false);
         props.navigation.navigate('Home');
       }
       setUsername(false);
     },
   );
   ```

2. **Fix Connection Confirmation Sequence**:
   ```javascript
   // Always show confirmation before connecting:
   if (qrCode.startsWith(LINK_PREFIXES.TICKET)) {
     const obj = parse(qrCode);
     setIsActive(false);
     showAlert(obj); // Always get confirmation first, regardless of connection status
   }
   ```

3. **Consolidate Deep Link Handlers**:
   - Create a centralized handler in `deep-links.js`
   - Register link types with callbacks from each component that needs to handle them
   - Remove duplicate linking event listeners

### Phase 2: Enhance Connection Reliability

4. **Add Connection Key Validation**:
   ```javascript
   // In SocketProvider.jsx, add validation before using stored keys:
   Keychain.getGenericPassword().then((credentials) => {
     if(credentials) {
       try {
         const val = credentials.password;
         const creds = JSON.parse(val);
         
         // Validate required fields exist
         if(!creds.host || !creds.port || !creds.token) {
           console.log('Invalid connection credentials');
           return;
         }
         
         credConnect(creds);
       } catch (e) {
         console.log('Error parsing stored credentials', e);
       }
     } 
   })
   ```

5. **Improve Connection Key Management**:
   - Create dedicated utilities for connection keys (similar to `keychain-store.js`)
   - Add proper error handling for storage operations
   - Implement backup/restore capability

6. **Add User Feedback on Connection States**:
   - Add visual indicators for connection state transitions
   - Provide context-aware UI elements to guide users through connection issues
   - Add success message before navigation

### Phase 3: Enhance First-Time Experience

7. **Add First-Run Detection**:
   ```javascript
   // In SocketProvider, detect first launch / no connection key:
   useEffect(() => {
     Keychain.getGenericPassword().then((credentials) => {
       if (!credentials) {
         // First time user with no connection key
         // Redirect to onboarding or help page
         Linking.openURL('https://mychips.org/nokey.html');
       } else {
         // Normal connection flow
         connectSocket();
       }
     });
   }, []);
   ```

8. **Create Offline Welcome Experience**:
   - Design minimal welcome screen with QR scanner access
   - Add basic offline guidance for new users
   - Include visual connections tutorial using icons (language-neutral)

## Implementation Plan

### ✅ Completed Tasks

- [x] 3.1 Implement first-run detection:
  - [x] 3.1.1 Add check for connection key presence on app start
  - [x] 3.1.3 Add reliable redirection to mychips.org/nokey.html for new users

- [x] 3.3 Fix initial tally loading with new connection:
  - [x] 3.3.1 Identify why tallies don't load on first connection with existing account
  - [x] 3.3.2 Implement targeted tally fetch after successful new token connection
  - [x] 3.3.3 Ensure fetch only happens for new connections, not routine reconnects

- [x] 1.1 Fix connection key preservation:
  - [x] 1.1.1 Remove the `resetGenericPassword()` call on connection error in Scanner component
  - [x] 1.1.2 Verify key reset happens only on successful path in connectSocket function
  - [x] 1.1.3 Add comments explaining the change to prevent future regressions

- [x] 1.2 Fix connection confirmation sequence:
  - [x] 1.2.1 Modify Scanner component to always show confirmation dialog before connection attempt
  - [x] 1.2.2 Update both URL and JSON connection paths for consistent user confirmation
  - [x] 1.2.3 Add comments explaining previous behavior and rationale for changes

### 🔲 Phase 1: Fix Remaining Critical Connection Bugs

- [ ] 1.3 Consolidate deep link handling:
  - [ ] 1.3.1 Create centralized link handler utility in deep-links.js
  - [ ] 1.3.2 Remove duplicate link listeners from SocketProvider and Home components
  - [ ] 1.3.3 Register callbacks for different link types in a single location

### 🔲 Phase 2: Enhance Connection Reliability

- [ ] 2.1 Add connection key validation:
  - [ ] 2.1.1 Add schema validation for connection keys
  - [ ] 2.1.2 Implement JSON parsing in try/catch
  - [ ] 2.1.3 Add required field validation
  - [ ] 2.1.4 Add graceful error handling for corrupted keys

- [ ] 2.2 Improve connection key management:
  - [ ] 2.2.1 Create `connection-keychain.js` utility (based on `keychain-store.js` pattern)
  - [ ] 2.2.2 Add proper error handling for storage operations
  - [ ] 2.2.3 Implement secure backup/restore capability similar to signing keys

- [ ] 2.3 Add user feedback mechanisms:
  - [ ] 2.3.1 Create toast/alert system for connection state changes
  - [ ] 2.3.2 Add success confirmation before navigation
  - [ ] 2.3.3 Implement connection status indicator in UI

### 🔲 Phase 3: Continue First-Time Experience Improvements

- [ ] 3.2 Create offline welcome experience:
  - [ ] 3.2.1 Design language-neutral welcome screen with icons
  - [ ] 3.2.2 Add scanner access button in prominent position
  - [ ] 3.2.3 Include visual guide for finding service providers

## Testing Strategy

1. **Connection Key Preservation Tests**:
   - Attempt connections with invalid tickets and verify old key is preserved
   - Test sequential connection attempts with different tickets
   - Verify app can recover from failed connection attempts

2. **Connection Flow Tests**:
   - Verify user confirmation always happens before connection attempt
   - Test alert dialog cancel/confirm behavior
   - Verify proper feedback during connection state transitions

3. **Deep Link Handling Tests**:
   - Test various URL formats and parameters
   - Verify no duplicate handling of the same URL
   - Test cold start vs. background app link handling

4. **First-Time Experience Tests**:
   - Verify app guidance when no connection key exists
   - Test first-run detection and workflow
   - Verify offline help resources are accessible

## Related Issues

- [Deep Linking - Android/iOS](deep-linking.md) - Integration with external scanner deep links
- [iOS Deep Links](ios_deeplinks.md) - iOS-specific deep link handling considerations

## Future Considerations

- Implement connection health monitoring with dead peer detection
- Create an offline mode with local operations queue that syncs when connection is restored
- Add connection diagnostics tool for users to troubleshoot issues
- Cache essential language data for better offline experience

### Known Edge Cases (Future Projects)

- **Key Loss on New Connection Failure**: 
  - Current behavior: When connecting with a new token, the old key is deleted before confirming the new connection works
  - Edge case: If user has working connection, scans an expired/invalid token, and confirms connection, they will lose both old and new keys
  - Impact: Low/Medium - Requires user to deliberately scan and confirm a bad token
  - Fix complexity: Medium-High - Would require restructuring connection flow to:
    1. Try connecting with new credentials first without deleting old key
    2. Only delete old key after confirming new connection is successful
    3. Handle fallback to old key if new connection fails
  - Recommendation: Address in future connection flow refactoring rather than as a quick fix
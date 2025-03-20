# Fix Deep Linking Issues in iOS After RN Update

## Issue Description
After updating from React Native 0.70.6 to 0.77.0, connection deep links work correctly on Android but fail on iOS simulators. The app launches from background to foreground but fails to establish connection.

Example connection deep link: `https://mychips.org/ticket?host=mychips.net&port=1025&token=a3fb51802cd7ebece95334e1e97c6de2&user=p1003`

## Analysis of Root Causes
1. **Conflicting Deep Link Handlers**: Both SocketProvider and Home components try to handle links
2. **Navigation Configuration Issue**: `getStateFromPath` in App.js always redirects to '/ticket'
3. **Incomplete External Format Support**: Not all external formats documented in `learn-message.md` are implemented
4. **URL Parsing Limitations**: Basic URL parsing doesn't handle special characters correctly
5. **iOS-Specific Considerations**: iOS has stricter URL handling than Android

## Strategic Approach

### 1. Consolidate Deep Link Handling
- Move all deep link handling logic to a single location
- Create a dedicated service/utility for processing links based on their type
- Remove duplicate `Linking.getInitialURL()` calls

### 2. Fix Navigation Configuration
- Update `getStateFromPath` to properly preserve the original path and parameters
- Map deep link types to correct screens based on URL pattern

### 3. Implement Complete External Format Support
- Add handlers for all documented formats: ticket, invite, pay, conkey, signkey, user, tally
- Follow documentation specifications for each format

### 4. Improve URL Parsing
- Replace custom parsing with more robust solutions
- Properly handle URL-encoded parameters
- Add validation for required parameters for each format

### 5. Add iOS-Specific Handling
- Add any iOS-specific initialization code needed for proper deep link handling
- Test with both iOS simulator and physical devices
- Add logging to trace deep link execution path

## Testing Plan
1. Create test deep links for each supported format
2. Test each link on both Android and iOS (simulator and physical device)
3. Test both cold start (app closed) and warm start (app in background) scenarios
4. Verify proper error handling for malformed links
5. Add automated tests where possible

## Success Criteria
- All deep link formats work consistently on both Android and iOS
- App properly parses parameters and establishes connection
- Error handling gracefully manages malformed links
- Documentation updated to reflect implementation details

## References
- [React Native Linking API](https://reactnative.dev/docs/linking)
- [React Navigation Deep Linking](https://reactnavigation.org/docs/deep-linking/)
- [MyCHIPs External Formats Documentation](../../doc/learn-message.md)
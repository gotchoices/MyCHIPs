# Signing Key Deep Link Implementation

## Issue Description
Currently, MyCHIPs mobile app only supports exporting signing keys in JSON format. While this method works for backups and some key transfers, we need to implement deep link support for sharing signing keys between devices as specified in the external formats documentation.

## Background
The deep-linking.md file outlines the implementation of various deep link formats for the MyCHIPs app. According to the `learn-message.md` documentation, signing keys should support both JSON and deep link URL formats:

```
Encrypted (standard):
LINK: 'https://mychips.org/signkey?s=...,i=...,d=...'
LINK: 'https://mychips.org/signkey?base64EncodedJSON'
JSON:
{
  signkey: {
    s: SALT,
    i: INITIALIZATION_VECTOR,
    d: ENCRYPTED_DATA (should decrypt to serialized JWK key)
  }
}
```

The app already has a solid key export implementation that handles:
- JSON file export (with proper encryption)
- QR code generation for the exported data
- Sharing functionality via the device's native sharing capabilities

However, the deep link format is not yet generated or properly handled when scanning.

## Use Cases

1. **Email Transfer**
   - User wants to email the key to themselves
   - QR code should be included in the email for scanning from another device
   - Deep link in the email enables direct import when clicked on mobile

2. **Physical Backup**
   - User wants to print the key on paper for secure offline storage
   - QR code is the primary element needed for this case
   - Some human-readable information for context is helpful

3. **Password Manager Storage**
   - User wants to copy the deep link and store it in a password manager app
   - Clean, copyable text format is required

4. **Text Message Transfer**
   - User wants to text the key to another device
   - Deep link is the most important element for this use case

5. **File System Backup**
   - User wants to download the JSON file (Android)
   - User wants to share the file to local storage app (iOS)
   - For transfer to SD cards or manual device transfer

## Proposed Implementation

### UI Design for Export Screen

```
+--------------------------------------------------+
|  Export                                     [X]  |
+--------------------------------------------------+
|                                                  |
|     +--------------------------+                 |
|     |                          |   [Share icon]  |
|     |       [QR CODE]          |                 |
|     |                          |                 |
|     +--------------------------+                 |
|                                                  |
|     https://mychips.org/signkey?  [Copy icon]    |
|                                                  |
|   File: [eyeball icon] (when disabled)           |
|                                                  |
+--------------------------------------------------+
|                                                  |
|   File: [eyeball icon] (when enabled)            |
|                                                  |
|     +--------------------------+                 |
|     | Textbox showing encrypted|  [Share icon]   | (ios only)
|     | key as JSON              |  [Download icon]| (android only)
|     +--------------------------+                 |
|                                                  |
+--------------------------------------------------+
```

The UI design uses minimal text and leverages existing icons for actions:
- QR code section is prominently displayed at the top for the most common use case
- URL display with copy icon for password manager and text message sharing
- File section is collapsible with an eyeball toggle to show/hide the advanced option
- Platform-specific actions (Share for iOS, Download for Android) are shown appropriately

### Implementation Checklist

1. **Key URL Generation** ✅
   - [x] Create `generateSignKeyURL` utility function to convert encrypted key data to URL format
   - [x] Properly encode URL parameters to handle all special characters
   - [ ] Support both direct URL parameter format and base64-encoded JSON format as a fallback for very large keys

2. **UI Implementation** ✅
   - [x] Redesign Export screen using the minimalist approach shown in the mockup
   - [x] Use standard icons (FontAwesome, SVG assets) for actions
   - [x] Implement clipboard functionality for the link section
   - [x] Make JSON text box scrollable and selectable
   - [x] Ensure proper truncation of long URLs with ellipsis
   - [x] Add collapsible section for the JSON file option
   - [x] Implement platform-specific actions (Share for iOS, Download for Android)
   - [x] Share both QR code and text link together

3. **Deep Link Handling** ✅
   - [x] Update deep-link configuration to properly register the `/signkey` path
   - [x] Remove obsolete "mychips://" prefix from App.js
   - [ ] Add default landing page on mychips.org
   - [x] Update apple-app-site-association file for iOS Universal Links
   - [x] Implement handler for signkey deep links to direct to Import Key screen
   - [x] Add robust URL parameter parsing with proper error handling

4. **Testing** 🧪
   - [x] Test copying link to clipboard
   - [x] Test sharing via email
   - [x] Test sharing via text messaging
   - [x] Test QR code scanning between devices
   - [x] Test deep link functionality when clicked
   - [x] Verify file download/sharing works correctly
   - [x] Test subsequent deep link handling
   - [ ] Test error handling for malformed data
   - [ ] Test on both Android and iOS platforms

## Implementation Notes

1. **URL Parameter Handling**
   - The URL parameters are properly escaped using `encodeURIComponent`
   - For extremely long keys, we should implement the base64-encoded JSON format as a fallback
   - Add URL length check and automatic format selection

2. **UI Components**
   - Used existing app components where possible:
     - ShareIcon from SvgAssets (enhanced with platform-specific rendering)
     - FontAwesome for copy icon
     - EyeIcon SVG for toggle
   - The collapsible JSON section preserves screen real estate
   - Made JSON text scrollable and selectable with black text on white background

3. **Deep Link Configuration**
   - Update the .well-known files on mychips.org to include signkey path configuration
   - Ensure both Android and iOS app configurations properly register the deep link handler
   - Look at the following files for current deep link handling:
     - App.js - contains URL scheme registration
     - deep-linking.md in issues folder - describes current implementation
     - Scanner component - handles QR code scanning

4. **Sharing Implementation**
   - Using react-native-share for sharing functionality
   - QR code sharing includes both image and text link
   - Using platform-specific UI (share on iOS, download on Android)
   - The ShareIcon component was updated to conditionally use different icons per platform

5. **Files Modified So Far**
   - /src/screens/Setting/GenerateKey/ExportModal/index.jsx
   - /src/components/SvgAssets/SvgAssets.jsx
   - /src/utils/file-manager.js
   - /src/screens/Tally/TallyPreview/index.jsx

6. **Files To Modify Next**
   - App.js - for URL scheme registration
   - Scanner component - for handling scanned QR codes
   - ImportKey screen - for processing deep link data

## Future Improvements

1. **Code Organization**
   - Review file organization between KeyManagement/GenerateKey and Setting/GenerateKey folders
   - Consider consolidating duplicate functionality

2. **Connection Key Export**
   - Implement similar export screen for connection keys
   - Provide a simplified UI in settings to show a deep link for the current connection key

3. **Base64 Fallback**
   - Implement the alternative `base64EncodedJSON` format for very long keys

4. **QR Code Optimization**
   - Research optimal error correction levels for QR codes containing key data
   - Consider adding a small logo or visual identifier to the QR code

5. **Multi-language Support**
   - Ensure all new text strings have proper language tags
   - Review and update existing translations

## Next Steps
1. **Deep Link Implementation**
   - Implement the deep link handler for the `signkey` format
   - Register the proper URL scheme in App.js
   - Add support for receiving and processing the deep link in the ImportKey screen
   - Test with real devices to ensure the link works properly when scanned or clicked

2. **Advanced Features**
   - Implement base64-encoded JSON format for very large keys
   - Add URL length detection and automatic format selection

3. **Testing & Documentation**
   - Complete thorough testing on both Android and iOS platforms
   - Test edge cases with malformed data and error handling
   - Update .well-known files on mychips.org to support the signkey path
   - Document the deep link format in relevant documentation

4. **Platform-Specific Optimizations**
   - Ensure optimal performance on both iOS and Android
   - Test with various Android versions and iOS devices

## Implementation Progress

### Phase 1: Export Implementation ✅
- Implemented key export functionality with URL format
- Added QR code generation for the exported signing key
- Implemented clipboard functionality for deep links
- Enhanced sharing capabilities for both QR code and link text
- Added support for platform-specific actions

### Phase 2: Import Implementation ⏳
- Implemented deep link handling in Scanner and Home components
- Added support for routing signing key deep links to ImportKey component
- Rewrote ImportKey component to improve state management and handle deep links
- Fixed issues with concurrent processing and duplicate toasts
- Preserved the original file import functionality

### Current Status
- Export functionality is fully working
- Import from deep links works reliably, including subsequent imports 
- Deep link configuration has been updated in App.js with all paths properly registered
- Removed obsolete "mychips://" URL scheme prefix
- Updated apple-app-site-association file for iOS Universal Links
- Added support for all major deep link types (signkey, invite, pay, ticket)
- Created centralized deep-links.js utility file for improved code organization
- Updated all components to use shared utility functions
- Feature is ready for comprehensive testing on real devices

### Technical Challenges Addressed
1. **Race Conditions in Redux Updates**: 
   - Fixed by rewriting ImportKey component to use refs for tracking state
   - Added proper state management to avoid duplicate Redux updates

2. **Duplicate Toasts**:
   - Resolved by improving the component lifecycle and state management
   - Used refs to prevent re-processing the same URLs

3. **Multiple Import Methods**:
   - Ensured the Import button always triggers file import flow
   - Deep links properly navigate to ImportKey component and show appropriate UI

4. **State Handling**:
   - Separated UI state from key data state
   - Introduced refs for tracking processed URLs to avoid render cycles
   - Improved error handling and cancellation

### Modified Files
- `/src/screens/Setting/GenerateKey/ExportModal/index.jsx` - Export UI
- `/src/screens/KeyManagement/ImportKey.jsx` - Import handling
- `/src/screens/KeyManagement/index.jsx` - Navigation processing
- `/src/screens/Scanner/index.jsx` - QR code handling
- `/src/screens/Home/index.jsx` - Deep link handling

### Current Code Implementation

1. **ImportKey Component**:
   ```javascript
   // Main changes to ImportKey component:
   const ImportKey = props => {
     // Using refs to track deep link processing state
     const isProcessingDeepLink = useRef(false);
     const processedUrls = useRef(new Set());
     
     // UI state and key data state separated
     const [uiState, setUiState] = useState({...});
     const [keyData, setKeyData] = useState({...});
     
     // Process URLs on component mount
     useEffect(() => {
       // Process signkey URL if available and not already processed
       const signkeyUrl = props.signkeyUrl || props.route?.params?.signkeyUrl;
       if (signkeyUrl && !processedUrls.current.has(signkeyUrl)) {
         processedUrls.current.add(signkeyUrl);
         isProcessingDeepLink.current = true;
         // Handle URL...
       }
       
       // Clean up refs on unmount
       return () => {
         isProcessingDeepLink.current = false;
         processedUrls.current.clear();
       };
     }, []);
     
     // Extract data from URL
     const extractKeyDataFromUrl = (url) => {
       // Parse URL parameters (s, i, d)
       // Return formatted JSON
     };
     
     // Store keys securely
     const storeKeys = async () => {
       // Update backend
       // Store in secure storage
       // Update Redux state
       // Reset component state
     };
   };
   ```

2. **Scanner Component**:
   ```javascript
   // Deep link handling in Scanner:
   else if (qrCode.startsWith(signkeyLink)) {
     // Currently missing UUID that other link types use
     props.navigation.navigate('Settings', {
       screen: 'KeyManagement',
       params: {
         signkeyUrl: qrCode,
         autoImport: true
       }
     });
   }
   ```

3. **Home Component**:
   ```javascript
   // Deep link handling in Home:
   else if(signkeyUri.has(host)) {
     // Also missing UUID for unique navigation
     props.navigation.navigate('Settings', {
       screen: 'KeyManagement',
       params: {
         signkeyUrl: url,
         autoImport: true
       }
     });
   }
   ```

### Implementation Insights

1. **Component Lifecycle**: Identified that the ImportKey component was not consistently remounting between deep link navigation events, which caused processing logic to run only once.

2. **State Persistence**: Discovered that React refs (`processedUrls.current`) persist across renders and remain populated even when navigation changes, preventing reprocessing of URLs.

3. **UUID Solution**: Implemented the same pattern used for other deep link types (payment, tally) that adds a random UUID to make each navigation unique, ensuring each URL is seen as new by React Navigation.

4. **ImportKey Improvements**: Modified the ImportKey component to respond to URL dependency changes instead of relying on component mounting, making it more robust for handling repeated deep links.

### Remaining Tasks
1. **Update Android App Links Configuration**: ✅
   - Added the `/signkey` path to the intent filter in Android's `AndroidManifest.xml`
   - Fixed issue where deep links weren't working on real Android devices
   - The full intent filter now properly includes all path patterns:

```xml
<!-- Updated in AndroidManifest.xml -->
<intent-filter android:autoVerify="true">
  <action android:name="android.intent.action.VIEW" />
  <category android:name="android.intent.category.DEFAULT" />
  <category android:name="android.intent.category.BROWSABLE" />
  <data android:scheme="https" />
  <data android:host="mychips.org" />
  <data android:pathPattern="/ticket" />
  <data android:pathPattern="/invite" />
  <data android:pathPattern="/pay" />
  <data android:pathPattern="/signkey" /> <!-- Added this line -->
</intent-filter>
```

2. **Testing on Real Devices**:
   - After updating AndroidManifest.xml, rebuild and reinstall the app
   - Verify App Links in Android Settings > Apps > [Your App] > Open by default
   - Test deep links via camera app and direct browser URLs
   - Check logcat output for any verification errors
   - Test on both iOS and Android physical devices
   - Verify handling of edge cases and malformed inputs
   - Ensure proper performance across different platforms

3. **Additional Information About assetlinks.json**:
   - The server's assetlinks.json file is correctly configured with:
     - Package name: "org.mychips.chark"
     - Proper SHA-256 certificate fingerprint
   - No changes needed to assetlinks.json since we're just adding a new path
   - The file establishes the relationship between domain and app, not individual paths

4. **Documentation**:
   - Add usage examples for developers
   - Document the implementation details in the project wiki

5. **Advanced Features** (Future):
   - Implement base64-encoded JSON format for very large keys
   - Add automatic format selection based on key size
   - Enhance error handling for malformed deep links

### Strategy for Fixing Subsequent Deep Link Imports

After analyzing the code and seeing the existing pattern in the app for handling recurring deep links, we have a clear solution:

1. **Use UUID Approach from Payment and Tally Links**:
   - We discovered that the Scanner component already has a reliable mechanism for handling repeated QR code scans
   - For payment links: `const payUrl = ${qrCode}&randomString=${uuid()};`
   - For tally invites: `const tallyInviteUrl = ${qrCode}&randomString=${uuid()};`
   - These add a random UUID to ensure each navigation is seen as unique

2. **Implementation Plan for Signkey Links**:
   ```javascript
   // In Scanner component
   else if (qrCode.startsWith(signkeyLink)) {
     // Add random UUID to ensure each scan is processed uniquely
     const uniqueSignkeyUrl = `${qrCode}&randomString=${uuid()}`;
     props.navigation.navigate('Settings', {
       screen: 'KeyManagement',
       params: {
         signkeyUrl: uniqueSignkeyUrl,
         autoImport: true
       }
     });
   }
   
   // Also update Home component similarly for clicked links
   else if (signkeyUri.has(host)) {
     const uniqueSignkeyUrl = `${url}&randomString=${uuid()}`;
     props.navigation.navigate('Settings', {
       screen: 'KeyManagement',
       params: {
         signkeyUrl: uniqueSignkeyUrl,
         autoImport: true
       }
     });
   }
   ```

3. **Simplify ImportKey Component**:
   - Remove all URL tracking via processedUrls - it's no longer needed
   - Keep a simple isProcessing flag to prevent concurrent operations
   - Process each incoming URL directly without checking if it's been seen before
   - Keep the effect dependency on the URL to ensure it runs when the URL changes

4. **Why This Works**:
   - The UUID ensures each navigation has a different URL parameter
   - React Navigation will see this as a new route, triggering effects with URL dependencies
   - Even if the component isn't unmounting, the effect will re-run with the new unique URL
   - This matches the existing pattern in the app that's working for other link types

5. **Advantages of This Approach**:
   - Follows established patterns in the existing codebase
   - Works regardless of navigation stack behavior
   - Simple to implement and maintain
   - Doesn't require complex state management

### Next Testing Steps
1. Implement the UUID approach for signkey links in both Scanner and Home components
2. Remove URL tracking in ImportKey, rely only on the URL dependency in useEffect
3. Test multiple deep link scenarios:
   - Same URL multiple times
   - Different URLs in sequence
   - Interrupted imports (cancellation)
   - Manual import between deep links

### Follow-up Tasks
1. Complete server configuration for the landing page on mychips.org

### Completed Code Refactoring (Phase 3) ✅
We've successfully implemented the consolidation phase:

1. **Created `utils/deep-links.js` Utility File**:
   - Centralized deep link parsing logic in one utility file
   - Included common constants and patterns for all deep link types
   - Provided helper functions for parsing, validating, and processing URLs:
     - `LINK_TYPES` and `LINK_PREFIXES` constants
     - `addUuidToUrl()` for adding unique identifiers to URLs
     - `extractPathType()` for determining link types
     - `parseSignkeyUrl()` for processing signkey URLs

2. **Updated Existing Components**:
   - Modified Scanner component to use our utility functions
   - Updated Home component to use centralized path extraction
   - Refactored ImportKey component to use shared URL parsing
   - Preserved the unique handling logic in each component

3. **Benefits Achieved**:
   - Improved code organization and reusability
   - Easier maintenance and future extensions
   - Consistent URL handling across the application
   - Reduced code duplication
   - Better separation of concerns between components

This refactoring was done incrementally and carefully, ensuring that all existing functionality continues to work while making the code more maintainable and easier to extend with new deep link types in the future.

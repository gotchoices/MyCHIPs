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

3. **Deep Link Handling** ⏳
   - [ ] Update deep-link configuration to properly register the `/signkey` path
   - [ ] Remove obsolete "mychips://" prefix from App.js
   - [ ] Add default landing page on mychips.org
   - [ ] Further details needed in .well-known/* files on mychips.org?
   - [ ] Implement handler for signkey deep links to direct to Import Key screen
   - [ ] Add robust URL parameter parsing with proper error handling

4. **Testing** 🧪
   - [x] Test copying link to clipboard
   - [x] Test sharing via email
   - [x] Test sharing via text messaging
   - [ ] Test QR code scanning between devices
   - [ ] Test deep link functionality when clicked
   - [ ] Verify file download/sharing works correctly
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
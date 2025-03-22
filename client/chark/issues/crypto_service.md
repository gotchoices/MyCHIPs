# Crypto Service Implementation and Migration Plan

*Last updated: March 22, 2025*

## Background

After migrating from React Native 0.70.6 to 0.77.0, the WebCrypto API functionality broke, causing issues particularly with key export/import operations. The app previously used `react-native-webview-crypto` but has been updated to use `react-native-quick-crypto` as noted in the iOS deeplinks issue documentation.

## Current Problem

Despite `QuickCrypto.install()` being called in App.js, components using WebCrypto APIs (`window.crypto.subtle`) are experiencing errors:

```
Error in deriveKey: Error: WebCrypto API is not available. Make sure QuickCrypto.install() is called before encryption.
```

This suggests that the WebCrypto API is not properly being made available to all modules.

## Investigation Findings (March 22, 2025)

We conducted a detailed investigation and found:

1. **Partial Subtle Implementation**: QuickCrypto implements most of the WebCrypto subtle API functions, but not all:
   - ✅ Implemented: `generateKey`, `exportKey`, `importKey`, `sign`, `verify`, `encrypt`, `decrypt`
   - ❌ Missing: `deriveKey` (critically needed for key export)

2. **Code Inspection**: Logging the available subtle methods from SocketProvider:
   ```
   Wyseman subtle methods: []
   subtle.generateKey type: function
   subtle.exportKey type: function
   subtle.importKey type: function
   subtle.sign type: function
   subtle.verify type: function
   subtle.deriveKey type: undefined
   subtle.encrypt type: function
   subtle.decrypt type: function
   ```

3. **Implementation Gap**: This explains why:
   - Websocket authentication works (uses generateKey, sign, etc.)
   - Key export fails (depends on deriveKey which is undefined)

4. **react-native-webview-crypto Confusion**: After removing this package, we found it was automatically modifying `global.crypto.subtle` when loaded, providing its own implementation of the missing functions.

## Further Analysis (March 22, 2025 Update)

After a comprehensive review of the codebase, we've identified remaining references to global crypto objects that need to be updated:

1. **SocketProvider.jsx**:
   - Still directly referencing `global.crypto || window?.crypto` on line 49
   - This should be updated to use the crypto service instead

2. **file-manager.js**:
   - Using `crypto.getRandomValues` directly on line 94
   - Should use a crypto service method

3. **In services/crypto.js itself**:
   - Using `window.crypto?.subtle || global.crypto?.subtle` on line 42
   - Using `crypto.getRandomValues` directly on lines 99 and 138
   - These should use QuickCrypto's functions directly

4. **message-signature.js**:
   - Still getting the subtle interface directly via `getSubtle()` on line 10
   - Should fully embrace the service pattern

## Solution Strategy: Centralized Crypto Service

We've implemented a centralized crypto service approach to solve this problem:

1. Create a single module (`src/services/crypto.js`) that initializes the crypto environment once
2. Expose standardized functions for all crypto operations
3. Update components to use these functions instead of accessing WebCrypto directly
4. Implement custom `deriveKey` functionality using QuickCrypto's available `pbkdf2` functions

### Benefits of this approach:

- Centralizes crypto initialization in one place
- Ensures consistent access patterns across the app
- Makes it easier to debug issues
- Makes it easier to swap out implementations in the future
- Provides fallbacks for missing functionality

## Implementation Progress

### ✅ Completed

1. Created a new crypto service at `src/services/crypto.js` with:
   - Initialization functions
   - Key generation and export/import functions
   - Encryption/decryption functions
   - Proper error handling

2. Updated App.js to use the crypto service:
   ```javascript
   // Old approach
   global.Buffer = Buffer;
   QuickCrypto.install();
   
   // New approach
   import { initCryptoService } from './src/services/crypto';
   initCryptoService();
   ```

3. Partially refactored components to use the crypto service:
   - Started using crypto service functions in several files
   - Enhanced error handling and user feedback
   - Removed react-native-webview-crypto dependency

### 🔲 Pending Items (Prioritized Checklist)

1. **Phase 1: Complete Direct References Cleanup**
   - [x] 1.1 Add `getRandomValues` function to crypto.js service
   - [x] 1.2 Update file-manager.js to use crypto.getRandomValues instead of direct calls
   - [x] 1.3 Update crypto.js to use its own getRandomValues function
   - [x] 1.4 Update SocketProvider.jsx to use crypto service
   - [x] 1.5 Clean up message-signature.js to fully use the service pattern

2. **Phase 2: Implement Custom deriveKey Function**
   - [x] 2.1 Create a custom implementation of deriveKey using QuickCrypto's pbkdf2
   - [x] 2.2 Ensure the interface matches the current usage (returns [key, salt])
   - [x] 2.3 Make key objects compatible with encrypt/decrypt operations

3. **Phase 3: Testing**
   - [x] 3.1 Test key generation functionality
   - [x] 3.2 Test key import/export functionality
   - [x] 3.3 Test file sharing and QR code generation
   - [x] 3.4 Verify signing and verification work correctly

4. **UI Improvements (Extended Scope)**
   - [x] 4.1 Simplify key generation flow by removing forced export step
   - [x] 4.2 Simplify key import flow by removing forced export step
   - [x] 4.3 Improve file export by showing filename in success message
   - [x] 4.4 Make PassphraseModal more compact and adapt to its content
   - [x] 4.5 Customize PassphraseModal based on context (single field for import, validation for export)
   - [x] 4.6 Disable Export button until passphrases match

5. **Future Improvements (After Merge)**
   - [x] 5.1 Update to standard 'buffer' package
   - [ ] 5.2 Add more comprehensive error handling and logging
   - [ ] 5.3 Consider TypeScript type definitions for crypto functions

## Technical Implementation Details

### 1. Add getRandomValues to Crypto Service

```javascript
/**
 * Generate random values (replacement for crypto.getRandomValues)
 * @param {TypedArray} array - The array to fill with random values
 * @returns {TypedArray} - The array filled with random values
 */
export const getRandomValues = (array) => {
  // Use QuickCrypto's randomFillSync function
  return QuickCrypto.randomFillSync(array);
};
```

### 2. Custom deriveKey Implementation

```javascript
/**
 * Derive a key from a password and salt
 * @param {string} password - The password to derive from
 * @param {Uint8Array} [salt] - The salt to use (generated if not provided)
 * @returns {Promise<Array>} - [derivedKey, salt]
 */
export const deriveKey = async (password, salt) => {
  try {
    // Generate a random salt if not provided
    const useSalt = salt || getRandomValues(new Uint8Array(8));
    
    // Use QuickCrypto's pbkdf2 directly
    const derivedKeyBuffer = await QuickCrypto.pbkdf2Sync(
      Buffer.from(password),
      useSalt,
      10000,
      32, // 256 bits
      'sha256'
    );
    
    // Create a key object compatible with encrypt/decrypt
    // This may require some additional work to ensure compatibility
    const key = {
      // Implementation will depend on what encrypt/decrypt expect
      // May need to use QuickCrypto.createSecretKey or similar
    };
    
    return [key, useSalt];
  } catch (error) {
    console.error('Error deriving key:', error);
    throw error;
  }
};
```

## Testing Strategy

After all components are updated:

1. Test all key-related operations:
   - Key generation
   - Key import
   - Key export/save
   - Signing operations

2. Test specifically the Export functionality that was failing:
   - Creating a passphrase
   - Exporting keys to file
   - Sharing keys via QR

3. Test edge cases:
   - Behavior when the app starts offline
   - Recovery from failed crypto operations

## Branching Strategy

1. Create a new branch for current changes: `crypto-service-implementation`
2. Commit current state to have a stable checkpoint
3. Complete the Phase 1 checklist items
4. Implement deriveKey (Phase 2)
5. Test thoroughly (Phase 3)
6. Merge back to dev when all tests pass

## Reference Materials

1. React Native WebCrypto API:
   - Issue with subtle crypto in RN 0.77.0: https://github.com/facebook/react-native/issues/41487

2. QuickCrypto Documentation:
   - GitHub repo: https://github.com/margelo/react-native-quick-crypto
   - Installation guide: https://github.com/margelo/react-native-quick-crypto#-installation
   - Available functions: QuickCrypto provides pbkdf2/pbkdf2Sync functions as direct alternatives to subtle.deriveKey

3. WebCrypto API documentation:
   - MDN Web Docs: https://developer.mozilla.org/en-US/docs/Web/API/Web_Crypto_API

4. QuickCrypto Implementation Details:
   - QuickCrypto does implement most subtle methods but is missing critical `deriveKey` functionality
   - The implementation can be found in `/node_modules/react-native-quick-crypto/lib/commonjs/subtle.js`
   - `install()` function in index.js sets `global.crypto = QuickCrypto`
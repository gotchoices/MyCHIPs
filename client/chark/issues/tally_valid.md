# Tally Validity and Verification Implementation

*Last updated: April 2, 2025*

## Background

The MyCHIPs platform uses cryptographic signatures to ensure the validity and integrity of tallies and chits. When tallies are created, each user adds their public signing key to the tally (in the certificate property), and when both parties have signed a common version, the tally is considered valid. During development and testing, some tallies have been created without valid keys or signatures, and in some cases, users have lost or regenerated their signing keys.

Currently, the application does not verify the cryptographic validity of tallies and chits when they are loaded from the backend. The database contains a field (typically called 'json' or 'json_core') that holds the exact data that was signed, making it possible to verify signatures in the client application.

## Current Problems

1. **No Validity Verification**: The app doesn't verify signatures on tallies or chits when loading them
2. **Key Mismatch Detection**: No warning when a tally was signed with a different key than currently loaded
3. **Chit Chain Integrity**: No verification of the chit hash chain integrity
4. **Missing UI Indicators**: No visual indicators for different validity states

## Implementation Goals

1. Add two separate verification checks for tallies and chits:
   - **Signature Validity**: Verify if the signature is cryptographically valid
   - **Key Match**: Check if the key used matches the user's current active key

2. Display validity status in the UI:
   - Green check: Valid signature with matching key
   - Yellow warning: Valid signature but key mismatch (signed with old/different key)
   - Red warning: Invalid signature (missing key, missing signature, or failed verification)

3. Show detailed validity information in tally and chit detail screens
4. Verify chit hash chain integrity
5. Create a debug utility for re-signing tallies and chits (for testing only)

## Technical Details

### Tally Structure
- Tallies contain public keys in certificate properties
- Each party signs the tally's JSON representation
- The signature is stored in the database

### Chit Chain Structure
- The tally acts as "block zero" in a hash chain
- Each chit is like a block containing:
  - `chain_prev`: Digest of the prior block
  - `chain_idx`: Sequential number in the hash chain
  - `chain_dgst`: Hash of the chit's content
- As trading partners reach consensus, chits are assigned matching chain_idx values
- The final chain_dgst represents a checksum of the entire tally history

## Implementation Strategy

### Phase 1: Verification Implementation (Core Functionality)
1. Add json/json_core fields to existing tally and chit queries
2. Create verification utility functions in a dedicated module:
   - **isSignatureValid**: Verify if a tally/chit has a cryptographically valid signature
   - **isKeyMatch**: Check if the key used matches the user's current key
   - **getVerificationStatus**: Return both validity and key match status
   - Chit hash chain verification

### Phase 2: Basic UI Integration (Home Screen)
1. Create reusable `ValidityIndicator` component with different states:
   - Valid signature + matching key (green)
   - Valid signature + mismatched key (yellow)
   - Invalid signature (red)
2. Add these indicators to tally items in the home screen
3. Keep the implementation non-disruptive to existing functionality

### Phase 3: Detailed View Integration
1. Add validity details section to tally view screens:
   - Show both signature validity and key match status
   - Provide explanation of what each status means
   - Add action buttons based on status (e.g., re-sign if key mismatch)
2. Implement similar indicators for chit history screen
3. Add chain integrity visualization to chit detail screens

### Phase 4: Testing and Debug Tools (Optional)
1. Create specialized functions for re-signing tallies and chits
2. Implement backend support for re-signing operations
3. Add a debug-only interface for performing these operations

## Implementation Plan

### ✅ Completed
- Initial analysis of the required changes
- Created tally verification utility (src/utils/tally-verification.js)
- Initial testing of verification with real tallies
- Created a test analyzer for deeper debugging (src/utils/tally-test.js)

### ✅ Implemented
- Added warning icons to the Home screen's tally display
- Added proper Redux integration for tally validation statuses
- Implemented separate updataTallySlice for storing validation statuses
- Fixed reactivity issues with asyncronous validation and UI updates
- Ensured validation results persist through app state updates
- Made warning indicators show only for tallies with actual issues

### 🔄 Current Progress
We have successfully implemented:
- Proper Redux integration for tally validation
- Fixed the reactivity issue with asynchronous validation
- Separated validation logic to make it maintainable
- Created a pattern for validation that can be reused for chits
- Ensured warnings only show for tallies with actual issues

### Next Steps

1. Add tooltips to the warning indicators:
   - Show a tooltip when hovering over the warning icon
   - Explain what the warning means (invalid signature, key mismatch)
   - Include simple instructions on how to address the issue

2. Add detailed validity information to the tally detail screen:
   - Create a dedicated section showing validity status
   - Show both signature validity and key match status separately
   - Include explanation of what each status means
   - Add potential actions (e.g., re-sign with current key)

3. Implement different warning levels based on severity:
   - Yellow for key mismatch (warning)
   - Red for invalid signature (error)
   - Use appropriate icons for each level

4. Consider chit validation as a future enhancement:
   - Apply similar validation pattern to chits
   - Verify chit signatures
   - Validate the hash chain integrity

5. Add testing:
   - Create unit tests for validation functions
   - Test with different tally scenarios (valid, invalid, key mismatch)
   - Manual testing with real-world tallies

### 🔲 Pending Items (Prioritized Checklist)

#### Phase 1: Foundation
- [x] 1.1 Initial implementation of tally verification functionality:
  - [x] 1.1.1 Implement `verifyTallySignature(tally)` function for basic verification
  - [x] 1.1.2 Implement `checkKeyMatch(tally)` function for key comparison
  - [x] 1.1.3 Add a preliminary `getTallyValidityStatus(tally)` function
  - [x] 1.1.4 Create a test analyzer for verification debugging
  
- [x] 1.2 Refine verification to separate concerns:
  - [x] 1.2.1 Clean up `verifyTallySignature(tally)` for cryptographic validity
  - [x] 1.2.2 Keep separate `checkKeyMatch(tally)` function for key comparison
  - [x] 1.2.3 Use `getTallyValidityStatus(tally)` to return appropriate status indicators
  - [x] 1.2.4 Add clear documentation for each function and status type

- [x] 1.3 Create a non-disruptive approach to enrich tally data with verification results:
  - [x] 1.3.1 Created `enhanceTalliesWithValidity` function for batch processing
  - [x] 1.3.2 Add validity status to tally objects
  - [x] 1.3.3 Ensure this doesn't disrupt existing tally data structures

- [x] 1.4 Update existing Redux slices to include verification:
  - [x] 1.4.1 Enhanced `openTalliesSlice.js` to perform verification after fetching tallies
  - [x] 1.4.2 Created new `updateTallySlice.js` to centralize validation state management
  - [x] 1.4.3 Made validation happen asynchronously without blocking UI

- [x] 1.5 Confirm necessary field requirements:
  - [x] 1.5.1 Confirmed `json_core` is correct field for signature verification
  - [x] 1.5.2 Confirmed `hold_sig` is the correct signature field
  - [x] 1.5.3 Added correct field list to tally fetching

- [x] 1.6 Improve error handling for validation:
  - [x] 1.6.1 Properly handle type differences in validation comparison
  - [x] 1.6.2 Add clear error reporting for validation failures
  - [x] 1.6.3 Ensure proper handling of missing fields during validation
  - [x] 1.6.4 Test with various tally formats and data

#### Phase 2: Basic UI Integration
- [x] 2.1 Create a reusable validity indicator component:
  - [x] 2.1.1 Implementation of simple indicator that shows warning for any validity issues
  - [x] 2.1.2 Created `Warning_16` icon with consistent naming convention
  - [x] 2.1.3 Added it in a non-disruptive way (tooltips will be added in future updates)
  - [ ] 2.1.4 (Future) Review and update other icons to follow the same naming pattern (e.g., Icon_NativeSize)

- [ ] 2.2 Integrate validity indicators into appropriate screens:
  - [x] 2.2.1 Located the Home screen's `TallyItem` component in `src/screens/Tally/TallyItem/index.jsx`
  - [x] 2.2.2 Added the Warning_16 component to display validity warning
  - [x] 2.2.3 Positioned it alongside the name without disrupting the existing layout
  
- [ ] 2.3 Extend validity indicators to additional screens (if needed):
  - [ ] 2.3.1 Identify other screens where tallies are displayed
  - [ ] 2.3.2 Add validity indicators in a consistent way
  - [ ] 2.3.3 Test with tallies in various validity states

#### Phase 3: Detailed Views
- [ ] 3.1 Add tally validity details to the tally detail screen:
  - [ ] 3.1.1 Identify the appropriate section in `src/screens/Tally/index.jsx`
  - [ ] 3.1.2 Create a collapsible "Validity Information" section
  - [ ] 3.1.3 Show separate sections for signature validity and key match status
  - [ ] 3.1.4 Add buttons for actions based on validation status (e.g., re-sign option)

- [ ] 3.2 Implement chit validity indicators in the chit history screen:
  - [ ] 3.2.1 Enhance `src/screens/Tally/ChitHistory/index.jsx` with validity indicators
  - [ ] 3.2.2 Show chain status (chained/unchained) in the chit list
  - [ ] 3.2.3 Highlight chain anomalies (missing or incorrect chain_idx)

- [ ] 3.3 Add chain integrity visualization to the chit detail screen:
  - [ ] 3.3.1 Enhance `src/screens/Tally/ChitDetail/index.jsx` 
  - [ ] 3.3.2 Add a section showing chain_prev, chain_idx, and chain_dgst
  - [ ] 3.3.3 Visualize the chit's position in the overall chain
  - [ ] 3.3.4 Highlight any chain integrity issues

- [ ] 3.4 Add explanatory text for verification statuses:
  - [ ] 3.4.1 Create clear explanations for each verification state
  - [ ] 3.4.2 Add language to explain the difference between validity and key match
  - [ ] 3.4.3 Use the existing HelpText component for consistency

#### Phase 4: Re-signing Utility (For Testing)
- [ ] 4.1 Design a developer-only interface for re-signing operations:
  - [ ] 4.1.1 Create a dedicated screen accessible only in development builds
  - [ ] 4.1.2 Show separate options for different re-signing scenarios
  - [ ] 4.1.3 Add clear warnings about the consequences of re-signing

- [ ] 4.2 Implement client-side re-signing functions:
  - [ ] 4.2.1 Create functions to re-sign tallies with current keys
  - [ ] 4.2.2 Create functions to rebuild and re-sign the chit chain
  - [ ] 4.2.3 Add thorough error handling and validation
  - [ ] 4.2.4 Test with different tally and chit configurations

- [ ] 4.3 Backend integration for re-signing:
  - [ ] 4.3.1 Work with backend team to define the API for re-signing operations
  - [ ] 4.3.2 Create API requests to handle tally and chit updates
  - [ ] 4.3.3 Implement safeguards against accidental use

- [ ] 4.4 Testing and safeguards:
  - [ ] 4.4.1 Add environment detection to prevent use in production
  - [ ] 4.4.2 Add confirmation dialogs for irreversible operations
  - [ ] 4.4.3 Test thoroughly with various tally and chit scenarios

## Testing Strategy

1. **Unit Tests**:
   - Test verification functions with known good/bad signatures
   - Test key comparison with matching/non-matching keys
   - Test chain verification with valid/invalid chains

2. **Integration Tests**:
   - Test with tallies in various states of validity
   - Test UI components with different validity states

3. **End-to-End Testing**:
   - Verify correct behavior across the application workflow
   - Test re-signing functionality in isolation

## Lessons from Initial Analysis

Our code review revealed that the application:
1. Signs tallies using json-stable-stringify on the tally's json_core
2. Verifies public keys match before signing
3. Has crypto utilities already in place that can be leveraged
4. Uses the backend-provided digest values rather than computing them locally

## Backend Data Investigation

We queried the backend database to understand what the tally data looks like, specifically focusing on json_core, hold_cert, and hold_sig fields:

### Investigation Method
```bash
ssh admin@mychips.net "psql mychips admin -c \"select json_core,hold_cert,hold_sig from mychips.tallies_v where tally_ent = 'p1004' and tally_seq = 46\""
```

### Key Findings

1. **Tally Structure**:
   - A tally has two sides: a "foil" and a "stock"
   - Each partner holds one side of the tally
   - The `hold_cert` field always represents the certificate of the current user (holder)
   - The `hold_cert` will match either the "foil.cert" or "stock.cert" in json_core, depending on which side the user holds
   - `tally_type` indicates whether the user holds the "foil" or "stock" side

2. **Valid Tallies (tally_seq = 46)**:
   - json_core contains complete tally data with both foil and stock certificates
   - Each certificate contains a public key needed for signature verification:
     ```json
     "public": {
       "x": "AIqSU6Rr1LXSQiT8ZGFJI95bwjixiqm_rkICtLRn1pGaXgAJyh0CuTYeYG8xM2DJtDu_nJuaFhOvrd26Ya-9cIAV",
       "y": "AUeB9P-7RfnNzv-UhD6iO7TN1S_SnGY3gA5a83cwJopLQ2o0q5bYajUtrUQekWRtFJhFHdyWbq04JwXJ9xbprH9n",
       "crv": "P-521",
       "ext": true,
       "kty": "EC",
       "key_ops": ["verify"]
     }
     ```
   - hold_sig contains a cryptographic signature of the json_core

3. **Different Signature Tallies (tally_seq = 42)**:
   - Similar structure but with a different public key and signature
   - Shows that verification must handle different keys

4. **Tallies Without Keys (tally_seq = 14)**:
   - public key is null in both json_core and hold_cert
   - hold_sig contains the string "Valid" rather than a cryptographic signature
   - These tallies need special handling in our verification logic

## Related Issues

- [Crypto Service Implementation](crypto_service.md) - We'll leverage the centralized crypto service

## Reference Materials

1. [WebCrypto API documentation](https://developer.mozilla.org/en-US/docs/Web/API/Web_Crypto_API)
2. [json-stable-stringify documentation](https://github.com/substack/json-stable-stringify)
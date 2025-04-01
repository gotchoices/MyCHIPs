# Payment Processing Improvements and Standardization

*Last updated: April 1, 2025*

## Background

The MyCHIPs mobile application handles payments between users through a digital signature process that ensures each transaction is cryptographically secure. During a detailed review of the payment flow, we identified several inconsistencies in how payment data is processed, particularly regarding units conversion, UUIDs, and memo fields.

## Current Issues

### 1. Inconsistent Units Conversion

The MyCHIPs application uses a decimal representation for display (e.g., 1.234 CHIPs) but requires integer values for storage and transaction processing (e.g., 1234 milliCHIPs). Currently, this conversion is handled inconsistently across the codebase:

- Some places use `round((chit ?? 0) * 1000, 0)` which returns a string with fixed decimal places
- Other areas use `parseInt(units) * 1000` which drops decimal places before multiplying
- There's no central constant for the conversion factor (1000) or decimal places (3)
- The ChitInput component has a custom decimal handling function that isn't fully aligned with the rest of the system

### 2. UUID Generation and References

When creating payment chits, UUIDs are generated using a combination of:
- Current date/time
- Random values
- Tally reference information

This approach works but lacks standardization across different payment types, potentially creating inconsistencies in how transactions are tracked and referenced.

Additionally, there are inconsistencies in how reference data is handled:
- In some components, reference is a state variable initialized as an empty object
- In some cases, reference is JSON stringified before being sent to the server
- In other cases, reference is used directly in the signed message
- The structure and expected format of the reference field is not well-documented

### 3. Memo Field Handling

The memo field for payments has inconsistent handling:
- Some flows properly capture and process user input
- Others have default values or transformation logic
- Character limits and validation are not uniformly applied

## Implementation Strategy

### 1. Standardize Units Conversion

- [x] Add constants to config/constants.js:
  - `CHIP_UNIT_FACTOR = 1000` (conversion factor from display to storage units)
  - `CHIP_DECIMAL_PLACES = 3` (number of decimal places to display)

- [x] Create utility functions in utils/common.js:
  - `chipsToUnits()` - Converts display CHIPs to integer units
  - `formatChipValue()` - Formats CHIP values with proper decimal places

- [x] Update all code paths to use these utility functions:
  - PaymentDetail/index.jsx
  - RequestDetail/index.jsx
  - Recieve/index.jsx
  - pay.js
  - ChitInput.jsx

### 2. Standardize UUID Generation and Reference Handling

- [x] Create a utility function for consistent chit UUID generation
- [x] Ensure all UUID generation follows the same pattern
- [x] Document the UUID format and purpose for future reference
- [ ] Verify UUID uniqueness across different payment scenarios
- [x] Standardize reference handling across components
  - Keep reference as a reactive state variable for future extension
  - Default reference to an empty object
  - Ensure reference is an object (not stringified) in the signed message
  - Ensure consistent handling of reference in API payloads

### 2a. Timestamp Format Standardization

- [x] Ensure consistent timestamp format across the application
- [x] Match server-side format: `YYYY-MM-DDTHH:mm:ss.SSSZ` in UTC timezone (matching PostgreSQL's `to_char(date AT TIME ZONE 'UTC', 'YYYY-MM-DD"T"HH24:MI:SS.FF3"Z"')`)
- [x] Create generateTimestamp() utility function for consistent ISO-8601 UTC dates
- [x] Use the utility function in all relevant components (PaymentDetail, TradingVariables)

### 3. Standardize Memo Field Handling

- [ ] Define consistent character limits and validation rules for memo fields
- [ ] Implement consistent memo field handling across all payment flows
- [ ] Add validation to ensure memos meet required formatting rules
- [ ] Document memo field expectations for developers

## Technical Details

### Units Conversion Implementation

The new utility functions ensure consistent handling of CHIP values:

```javascript
/**
 * Converts a floating-point CHIP value to integer milliCHIPs units
 * @param {number|string} chipValue - CHIP value with decimal places
 * @returns {number} Integer representing milliCHIPs units
 */
export const chipsToUnits = (chipValue) => {
  if (chipValue === null || chipValue === undefined || chipValue === '') {
    return 0;
  }
  
  // Parse the input to ensure it's a number
  const value = parseFloat(chipValue);
  if (isNaN(value)) {
    return 0;
  }
  
  // Convert to integer units
  return Math.round(value * CHIP_UNIT_FACTOR);
}

/**
 * Formats a CHIP value with the correct number of decimal places
 * @param {number|string} chipValue - CHIP value to format
 * @returns {string} Formatted CHIP value with proper decimal places
 */
export const formatChipValue = (chipValue) => {
  if (chipValue === null || chipValue === undefined || chipValue === '') {
    return '';
  }
  
  const value = parseFloat(chipValue);
  if (isNaN(value)) {
    return '';
  }
  
  return value.toFixed(CHIP_DECIMAL_PLACES);
}
```

### Payment Flow Diagram

The payment flow proceeds as follows:

1. **User Initiates Payment**:
   - From the Pay screen, user enters amount and memo
   - Input is validated and formatted with proper decimal places

2. **Payment Processing**:
   - Amount is converted to integer units using `chipsToUnits()`
   - UUID is generated for the chit
   - Transaction data is prepared and stringified

3. **Signature Creation**:
   - User authenticates via biometrics
   - Transaction data is signed with user's private key
   - Signature is attached to the payment

4. **Submission**:
   - Complete payment payload is sent to server
   - Server verifies signature and processes payment
   - UI shows success confirmation

## Success Criteria

- [ ] All amount conversions consistently use the centralized utility functions
- [ ] Payment flow correctly handles floating point to integer conversion
- [ ] Signatures are generated with integer units in the payload
- [ ] UUIDs are generated consistently across all payment types
- [ ] Memo fields have consistent validation and handling
- [ ] All changes are thoroughly tested across different payment scenarios

## Testing Strategy

1. **Unit Tests**:
   - Test utility functions with various input types and edge cases
   - Verify correct conversion between display and storage formats

2. **Manual Testing**:
   - Test payment flow with various decimal amounts (0.123, 1.000, 99.999, etc.)
   - Verify chit records in the database have correct integer units
   - Test edge cases (0, empty input, very large numbers)

## Action Items

1. [x] Add CHIP_UNIT_FACTOR and CHIP_DECIMAL_PLACES constants
2. [x] Implement chipsToUnits() and formatChipValue() utility functions
3. [x] Update PaymentDetail/index.jsx to use new utilities
4. [x] Update RequestDetail/index.jsx to use new utilities
5. [x] Update Recieve/index.jsx to use new utilities
6. [x] Update pay.js to use new utilities
7. [x] Update ChitInput.jsx to use formatChipValue()
8. [x] Standardize reference object handling across components
9. [x] Ensure proper UUID handling in payment flows
   - [x] Add chit_uuid to PaymentDetail payload
   - [x] Add chit_uuid to TradingVariables payload
   - [x] Remove unnecessary signature from RequestDetail
10. [x] Create standardized UUID generation utility 
    - [x] Created generateUuid() function for consistent UUID generation
    - [x] Created generateTimestamp() function for consistent date formatting
    - [x] Updated PaymentDetail to use these utility functions
    - [x] Updated TradingVariables to use these utility functions
    - [x] Added unitsToChips() function for the inverse conversion
    - [x] Updated ChitHistoryHeader to use unitsToChips() instead of hardcoded divisor
    - [x] Added missing chit_date field to TradingVariables payload
    - [x] Updated generateTimestamp to ensure consistent UTC format matching the server
11. [ ] Implement consistent memo field handling
12. [ ] Test changes thoroughly across all payment flows

## References

- [PaymentDetail Implementation](/src/screens/Tally/PaymentDetail/index.jsx)
- [RequestDetail Implementation](/src/screens/Tally/RequestDetail/index.jsx)
- [ChitInput Component](/src/components/ChitInput.jsx)
- [Message Signature Utilities](/src/utils/message-signature.js)
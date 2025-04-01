# Trading Variables Implementation and User Interface

*Last updated: April 1, 2025*

## Background

The MyCHIPs application allows users to configure trading variables that control how their tally relationships behave. These trading variables include target, bound, reward, and clutch settings, which together determine the behavior of tallies in the network.

Currently, the trading variables are set through a web-based form loaded in a WebView. When the user submits the form, the WebView intercepts the URL navigation and captures the form values, converts them into a signed chit, and sends them to the server.

## Current Issues

The trading variables configuration has several issues that need to be addressed:

1. **Data Type Handling**:
   - URL parameters from the WebView are received as strings
   - Initial implementation didn't properly convert these to numbers
   - This caused React Native bridge errors when the reference object was used

2. **Request Status**:
   - Setting chits currently lack a proper 'request' status
   - They should use 'good' like payment chits for consistency

3. **Units vs. Decimal Values**:
   - The web form should present values in CHIP units (with decimal places)
   - Values need to be converted to milliCHIPs (integers) before storage
   - Need to ensure consistent units conversion with the rest of the app

4. **User Interface**:
   - The web form needs visual improvements
   - Current layout could be more intuitive and match the app's design
   - Better feedback mechanisms needed for updates

## Implementation Strategy

### 1. Data Type Handling

- [x] Ensure URL parameters are explicitly converted to numbers
- [x] Implement numeric conversion with parseFloat() for all trading variables
- [x] Validate the values before including them in the reference object
- [x] Add proper error handling for invalid numeric values

### 2. Request Status and Type

- [x] Set request status to 'good' in trading variable chits
- [x] Fix the chit type from "tran" to "set" for proper signature validation
- [x] Verified that correct type and status enable successful processing
- [ ] Investigate why server initially marks settings chits as 'pend'

### 3. Units Conversion

- [ ] Update web form to display and accept values in CHIPs (decimal format)
- [ ] Implement consistent units conversion using the CHIP_UNIT_FACTOR constant
- [ ] Convert web form values to integer units before sending to the server
- [ ] Ensure values are properly displayed and formatted in the UI

### 4. User Interface Improvements

- [x] Add automatic navigation back after successful form submission
- [ ] Redesign the trading variables web form
- [ ] Add better descriptions and tooltips for each variable
- [ ] Implement input validation with visual feedback
- [ ] Add a confirmation step for significant changes
- [ ] Improve the visual design to match the app's aesthetic

## Technical Details

### Fixed URL Parameter Handling

The URL parameter handling was fixed by adding explicit numeric conversion:

```javascript
// Extract and convert parameters to numbers
const targetNum = parseFloat(params.target);
const boundNum = parseFloat(params.bound);
const rewardNum = parseFloat(params.reward);
const clutchNum = parseFloat(params.clutch);

// Build a reference object with the numeric values
const reference = {
  target: targetNum,
  bound: boundNum,
  reward: rewardNum,
  clutch: clutchNum
};
```

### Setting Request Status and Type

Updated the payload and JSON structure with the proper type and request status:

```javascript
// In the signed JSON object
const chitJson = {
  uuid,
  date,
  by: tally_type,
  type: "set", // Critical: Must be "set" not "tran" for proper signature validation
  tally: tally_uuid,
  ref: reference,
};

// In the API payload
const payload = {
  signature,
  reference,
  chit_type: 'set',
  chit_ent: tally_ent,
  chit_seq: tally_seq,
  chit_date: date,
  units: null,
  issuer: tally_type,
  chit_uuid: uuid,
  request: 'good', // Set request to 'good' like payment chits
};
```

## Success Criteria

- [x] Trading variables can be successfully updated without errors
- [x] Parameters are properly converted to numeric values
- [x] Automatic navigation provides a smooth user experience
- [ ] Values are properly converted between decimal and integer units
- [ ] The web form UI is intuitive and visually aligned with the app
- [ ] Changes are properly signed, recorded, and reflected in the system
- [ ] Error handling is robust and provides helpful feedback

## Testing Strategy

1. **Unit Tests**:
   - Test numeric conversion functions
   - Validate form parsing logic

2. **Integration Tests**:
   - Test end-to-end setting update flow
   - Verify signature generation and verification
   - Test with edge-case values (very large, very small, negative, etc.)

3. **UI Testing**:
   - Test form submission with various inputs
   - Verify validation provides appropriate feedback
   - Test responsive layout on different device sizes

## References

- [Trading Variables Component](/src/screens/Tally/TradingVariables/index.jsx)
- [Common Utilities](/src/utils/common.js)
- [WebView Documentation](https://github.com/react-native-webview/react-native-webview/blob/master/docs/Reference.md)
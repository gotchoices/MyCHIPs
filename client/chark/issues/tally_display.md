# Tally and Chit Display Improvements

*Last updated: April 4, 2025*

## Current Status Summary
- **ChipValue Component**: Enhanced to directly handle milliCHIP units with split integer/decimal styling
- **Internal Currency Conversion**: Implemented in ChipValue with Redux integration
- **Component Migration**: Banner, TallyItem and ChitHistory updated to use ChipValue (done)
- **ChitHistory Enhancements**:
  - Added date sorting toggle with correct running balance calculation
  - Implemented FieldFilterSelector component for status and chit_type filtering
  - Default to only showing 'good' status and 'lift'/'tran' type chits
  - Improved UI with more compact layout and better visualization
- **Next Focus**: 
  - Evaluate 'set' chit display in ChitHistory
  - Implement redux persistence for filter preferences
  - Update remaining components to use ChipValue
- **Current Branch**: dev
- **Related Files**: 
  - src/components/ChipValue/index.jsx (enhanced component)
  - src/components/FieldFilterSelector/* (new reusable filter component)
  - src/screens/Tally/Banner/index.jsx (updated with ChipValue)
  - src/screens/Tally/TallyItem/index.jsx (updated with ChipValue)
  - src/screens/Tally/ChitHistory/index.jsx (fully updated with sorting, filtering, and ChipValue)
  - src/screens/Tally/ChitHistory/ChitHistoryHeader/index.jsx (updated with ChipValue)
  - src/screens/Tally/index.jsx (modified to pass units)
  - src/redux/chipCurrencySlice.js (enhanced error handling)

## Background

The MyCHIPs mobile application displays financial information in various places, including tally lists, chit histories, and detail screens. We need to improve the consistency, readability, and functionality of these displays.

## Current Problems

1. **Inconsistent Value Display**: Different screens format and display CHIP values differently
2. **Inefficient Chit History**: Chit history shows settings chits and lacks options for sorting/filtering
3. **Manual Unit Conversion**: Many components manually convert between units and chips (dividing by 1000)
4. **Running Balance Issues**: Running balance display needs improvement in chit history
5. **Verbose UI Text**: Too much explanatory text clutters the UI in some screens

## Implementation Goals

1. Create standardized components for displaying CHIP values:
   - Consistent formatting with exactly 3 decimal places
   - Visual distinction between integer and decimal parts
   - Scalable for different screen contexts

2. Improve chit history display:
   - Filter out settings chits
   - Toggle sorting order
   - Show essential information only
   - Cleaner UI with better visual hierarchy

3. Standardize unit/chip conversions:
   - Use utility functions consistently (`unitsToChips`, `chipsToUnits`)
   - Ensure proper formatting with `formatChipValue` or `unitsToFormattedChips`

4. Fix running balance calculation and display:
   - Ensure accuracy in chit history
   - Consistent formatting with other CHIP values

## Implementation Strategy

### Phase 1: Standardized Conversion Utilities
1. Create/enhance utility functions for consistent value handling
2. Audit and update code to use these functions instead of manual calculations
3. Ensure all UI components display values consistently

### Phase 2: Chit History Improvements
1. Filter out settings chits from history view
2. Enhance chit item display for clarity and usability
3. Add sorting controls for different display orders
4. Fix running balance calculation and display

### Phase 3: Standardized CHIP Display Component
1. Create reusable component for displaying CHIP values
2. Style with underlined milliCHIPs for visual distinction
3. Support different sizes and contexts
4. Replace existing display patterns with the new component

## Pending Tasks

- [✅] Toggle ordering of chits in history view
- [✅] Make running balance display in chit history match the sort direction
- [🔄] Add filtering options to Chit History (similar to home screen)
  - [✅] Add basic UI for sort/filter controls
  - [✅] Implement reusable FieldFilterSelector component
    - Uses a BottomSheetModal approach rather than navigation screen
    - Generic design to work with any field (status, chit_type, etc.)
    - Supports multi-select with checkboxes
    - Avoids nested VirtualizedLists warning
    - Auto-generates SQL WHERE clauses
    - Uses "*" to indicate all options selected
  - [✅] Implement for status filtering in ChitHistory
  - [✅] Implement for chit_type filtering in ChitHistory  
  - [🔄] Store filter/sort preferences in Redux for persistence (basic functionality implemented, needs enhancement)
  - [ ] Add date range filtering option
  - [ ] Review 'set' chit display presentation in ChitHistory
  - [ ] Consider disabling running balance display when filtered (future enhancement)
    - Running balance may be misleading if some chits are filtered out
    - Add visual indicator when balance doesn't represent full tally
  - [ ] Retrofit existing filters to use FieldFilterSelector widget
    - [ ] Update Tally home screen filter to use FieldFilterSelector
    - [ ] Update Invite screen filter to use FieldFilterSelector
    - [ ] Evaluate other filter UI patterns for standardization
- [ ] Finish updating remaining components to use the ChipValue component
- [ ] Provide small and large variants of ChipValue for different screens
- [ ] Complete audit of manual unit conversion throughout the app
- [ ] Further improve visual hierarchy in tally list
- [ ] Clean up code by removing legacy currency conversion from parent components

## Progress

### ✅ Implemented
- Added filtering of settings chits in chit history
- Cleaned up chit item display in history
- Improved layout of chit history items
- Added `unitsToFormattedChips` utility function
- Updated `formatChipValue` to handle null values consistently
- Created standardized ChipValue component for CHIP value display
- Implemented consistent styling with integer/decimal part separation
- Added proper currency conversion directly in the ChipValue component
- Integrated ChipValue in Banner and TallyItem components
- Fixed Redux currency rate management for reactivity
- Restructured ChitHistory layout for better readability
- Reduced spacing between chit items to display more information

### 🔄 In Progress
- Replacing manual unit conversions with utility functions
- Creating responsive layout for mobile screens of different sizes
- Removing legacy currency conversion from parent components

### ✅ Recently Completed
- Added FieldFilterSelector component for multi-select filtering
  - Language-independent with symbols instead of English text
  - Supports both status and chit_type filtering
  - Uses BottomSheetModal for display
- Enhanced ChitHistory screen with:
  - Sorting toggle for date (ascending/descending)
  - Status filtering (default: 'good')
  - Chit type filtering (default: 'lift', 'tran')
  - Proper running balance calculation based on sort direction
- Extended ChipValue component to handle units directly
- Updated ChitHistory items to use ChipValue for running balance

## Components to Update
- ✅ TallyItem component in home screen - COMPLETED
- ✅ Banner component for total display - COMPLETED 
- ✅ ChitHistory display - COMPLETED
  - Header complete
  - Items updated to use ChipValue
  - Running balance display improved and using ChipValue
- ❌ ChitDetail display - NOT STARTED
- ❌ Profile displays - NOT STARTED
- ❌ Invite/tally creation screens - NOT STARTED
- ❌ Payment screens - NOT STARTED
- ❌ Other components displaying CHIP values - AUDIT NEEDED

## Reference
- CHIP_UNIT_FACTOR = 1000 (1 CHIP = 1000 milliCHIPs)
- CHIP_DECIMAL_PLACES = 3
- Available functions:
  - `unitsToChips(units)`: Convert milliCHIPs to floating-point CHIP value
  - `chipsToUnits(chipValue)`: Convert CHIP value to milliCHIPs
  - `formatChipValue(chipValue)`: Format with 3 decimal places
  - `unitsToFormattedChips(units)`: Convert and format in one step

## Future Opportunities

1. Standardize filter interfaces throughout the app using FieldFilterSelector
   - Replace existing FilterTallyList screen with FieldFilterSelector modal
   - Update Invite screen filter to use the same pattern
   - Create consistent look and feel across all filtering UIs

2. Enhance FieldFilterSelector component
   - Add support for date range filtering
   - Add support for numeric range filtering (for CHIP amounts)
   - Implement free text search for memo/reference fields
   - Create specialized filter types for different data types

3. Integrate with Redux for persistence
   - Create a dedicated filter reducer for app-wide filter state
   - Implement persistence across app restarts
   - Support default filter presets for different screens

4. Improve ChipValue component
   - Add interactive mode to show currency/unit details on tap
   - Consider supporting more decimal place display options
   - Add animation for value changes

5. Running balance improvements
   - Add indicators when running balance is affected by filters
   - Consider toggling running balance visibility when filters change
   - Optimize performance for large chit histories

## Feedback and Refinements

### Existing Design Patterns Analysis

#### Home Screen & Working Tallies Implementation
- **CHIP Value Display**:
  - Split display pattern: integer portion in larger font, decimal portion underlined in smaller font
  - Color coding: green for positive values, red for negative
  - Currency conversion display in smaller font above CHIP values
  - ChitIcon component used as a visual indicator

- **Sorting/Filtering**:
  - State-based sorting using Redux (filterTally in profileSlice)
  - Sort options: Recent, Ascending/Descending Balance, Absolute Balance, Alphabetical
  - Filter selection UI with SelectedIcon/UnSelectedIcon for visual feedback
  - Persistent filter settings using AsyncStorage

- **UI Components**:
  - FlatList with custom renderItem functions
  - Pull-to-refresh functionality
  - Empty state handling
  - Consistent spacing, padding, and visual hierarchy

#### Utility Functions
- `unitsToChips` and `chipsToUnits` for conversion
- `formatChipValue` for consistent 3-decimal formatting
- `unitsToFormattedChips` for one-step conversion and formatting
- `getIntegerValue` and `getDecimalValue` for styled display

### Additional Goals
1. **Create a Standardized CHIP Value Display Component**:
   - Extract the pattern from TallyItem/Banner into a reusable component
   - Support different sizes for different contexts
   - Consistent styling (large CHIPs, underlined milliCHIPs)
   - Include optional currency conversion display
   - Support color coding based on value sign
   - Simplify with internal currency conversion to reduce prop passing

2. **Remodel Chit History Display**:
   - Use the standardized CHIP component for all value displays
   - Add ordering options (date, amount, type)
   - Implement filtering capability (type, date range)
   - Fix running balance calculation and display
   - Apply consistent visual hierarchy

### Implementation Checklist
- [x] Extract CHIP display pattern into a reusable component
  - [x] Support integer/decimal split display
  - [x] Support optional currency conversion
  - [x] Support different sizes/contexts
  - [x] Apply consistent color coding

- [✅] Enhance Chit History screen
  - [✅] Implement sort toggle in ChitHistory filter bar
  - [✅] Create FieldFilterSelector component for filter UI
  - [✅] Apply standardized CHIP display to chit amounts
  - [✅] Apply standardized CHIP display to running balance
  - [✅] Maintain visual hierarchy (date, memo, amounts)
  - [✅] Add pull-to-refresh functionality

- [🔄] Improve filtering capabilities
  - [✅] Implement status filter using FieldFilterSelector
  - [✅] Implement chit type filter using FieldFilterSelector
  - [ ] Add date range filtering option
  - [ ] Add amount range filtering option

- [ ] Ensure consistent sorting implementation
  - [ ] Reuse Redux pattern for sort state management
  - [ ] Adapt sort utility functions for chit-specific fields
  - [ ] Implement persistent sorting preferences
  
- [✅] Code cleanup and optimization
  - [✅] Refactor ChipValue component to accept units parameter
  - [✅] Remove unused currency conversion code from parent components
  - [✅] Simplify ChipValue API by removing legacy props
  - [ ] Audit and optimize Redux selectors for performance
  - [ ] Add unit tests for currency conversion logic

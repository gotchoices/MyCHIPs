# Tally and Chit Display Improvements

*Last updated: April 4, 2025*

## Current Status Summary
- **ChipValue Component**: Enhanced to directly handle milliCHIP units with split integer/decimal styling
- **Internal Currency Conversion**: Implemented in ChipValue with Redux integration
- **Component Migration**: Banner, TallyItem, ChitHistory and ChitDetail updated to use ChipValue
- **ChitHistory Enhancements**:
  - Added date sorting toggle with correct running balance calculation based on chit_date
  - Implemented FieldFilterSelector component for status and chit_type filtering
  - Default to only showing 'good' status and 'lift'/'tran' type chits
  - Improved UI with more compact layout and better visualization
- **Filter Component Improvements**:
  - Created reusable FieldFilterSelector with Redux persistence
  - Replaced separate filter screens with modal approach
  - Applied to both Working Tallies and ChitHistory screens
- **Home Screen Sorting**:
  - Implemented three sorter widgets (name, date, balance) with toggle behavior
  - Created Redux-based state management with tallySortSlice
  - Removed obsolete FilterTallyList screen and related Redux code
  - Added visual indicators for active sorter
- **ChitDetail Enhancements**:
  - Updated to use ChipValue component with currency display
  - Added display of chain information (chain_idx, chain_prev, chain_dgst)
  - Removed hardcoded English strings in favor of message texts
  - Note: Needs comprehensive UI redesign in future for better UX
- **Certificate Detail Screen Improvements**:
  - Completely redesigned certificate detail display with sectioned layout
  - Added support for all certificate field types (contact, place, identity, public key, files)
  - Implemented interactive elements (clickable email, phone, web, address links)
  - Connected to Redux store for image display
  - Added proper error handling and fallbacks for all features
- **Next Focus**: 
  - **Immediate Priority (ChipValue Implementation):**
    - PendingChits components - Replace formatChipValue with ChipValue:
      - src/screens/Tally/PendingChits/Detail.jsx
      - src/screens/Tally/PendingChits/ChitItem.jsx
    - Invite screen - Use ChipValue for tally limits:
      - src/screens/Invite/index.jsx
      - src/screens/Invite/LimitContent/index.jsx

  - **Certificate Display Improvements:**
    - [✅] Enhance TallyCertificate screen:
      - [✅] Improve visual organization of certificate details
        - [✅] Create section boxes for different certificate components
        - [✅] Compact address display with unified place box
        - [✅] Display photo avatar in the file section
        - [✅] Add JSON-formatted public key display
        - [✅] Add interactive elements for email, phone, web and address fields
      - [✅] Fix remaining display issues:
        - [✅] Fix address icon display (Using FontAwesome's map-marker instead)
        - [✅] Fix launch functionality for contacts and addresses
          - [✅] Implemented openLink function with proper URL formatting
          - [✅] Added error handling and fallbacks
          - [✅] Configured different URL types (mailto:, tel:, https://, maps://)
          - [✅] Created separate handling for phone vs. cell numbers (call vs. text)
        - [✅] Fix avatar display in file items
          - [✅] Connected TallyCertificate to Redux imagesByDigest store
          - [✅] Used existing Avatar component with correct props (avatar not source)
          - [✅] Added fallback placeholder when images aren't in cache
          - [✅] Maintained digest display for debugging purposes
      - [ ] Add validation status indicators
      - [ ] Show repair options when applicable
        
      - [🔄] Enhance the existing avatar management system with a reusable DigestResource component:
        - [ ] Create a new component that leverages existing Redux infrastructure:
          - [ ] Implement in components/DigestResource/index.jsx
          - [ ] Build on top of existing avatarSlice and imagesByDigest Redux store
          - [ ] Utilize existing services for file fetching:
              - `tally.js`: fetchTallyFile, getHolderImage for tally-related images
              - `profile.js`: getFile, uploadImage for user profile images
          - [ ] Add support for multiple resource types beyond avatars
          - [ ] Include loading states and error handling
          - [ ] Support different display modes (avatar, full image, thumbnail)
          - [ ] Add configurable styling (size, shape, borders)
        
        - [ ] Maintain compatibility with existing image fetching pattern:
          - [ ] Keep working with the current fetchImagesByDigest thunk
          - [ ] Support the existing AsyncStorage caching mechanism
          - [ ] Ensure backward compatibility with current components
        
        - [ ] Apply enhanced component to certificate display screens:
          - [ ] Update TallyCertificate screen to use DigestResource for all file types
          - [ ] Support non-avatar images (identification documents, etc.)
          - [ ] Refactor CustomCertificateItem to use the same component
          
        - [ ] Consolidate avatar displays throughout the app:
          - [ ] Retrofit TallyGraphic to use the new component
          - [ ] Update Profile screen avatar displays
          - [ ] Keep compatibility with existing usage patterns
          
        - [ ] Improve the centralized avatar management system:
          - [ ] Add support for on-demand individual resource fetching
          - [ ] Enhance caching with expiration and refresh mechanisms
          - [ ] Optimize image loading with placeholders
      - [ ] Add validation status indicators
      - [ ] Show repair options when applicable
      - [ ] Ensure consistent style with other tally views

  - **Medium Priority (Filter UI Improvements):**
    - Retrofit remaining filter UIs to use FieldFilterSelector:
      - Activity Screen - Filter for tallies vs chits 
      - Tally/Search component - Add structured filtering
      - Tally/PendingChits - Filter options for pending chits
      - ProfileSlice filter - Migrate from direct AsyncStorage usage

  - **Long-term Tasks:**
    - Complete audit of all CHIP values in app and standardize
    - Comprehensive redesign of ChitDetail screen:
      - Improve overall aesthetics and user experience
      - Better organization of information
      - More intuitive layout for technical information
      - Visual indicators for chain integrity
    - Enhance TallyCertificate screen:
      - Add dedicated sections for different certificate components
      - Improve visual hierarchy of certificate properties
      - Add validation status indicators and repair options
      - Ensure consistent style with other tally views
    - Add date range filtering to ChitHistory

  - **Completed Tasks:**
    - ✅ ChitDetail screen updated with ChipValue
    - ✅ Chain information (chain_idx, chain_prev, chain_dgst) added to ChitDetail
    - ✅ 'set' chit display works correctly in ChitHistory
    - ✅ Home screen sorting implemented with tallySortSlice
    - ✅ Removed obsolete FilterTallyList screen and Redux code
    - ✅ Removed obsolete language tags ('sort.ddate', 'sort.dbal', 'sort.abal', 'sort.mbal', 'sort.dname', 'sort')
- **Current Branch**: dev
- **Related Files**: 
  - **Components**:
    - src/components/ChipValue/index.jsx (enhanced component for CHIP value display)
    - src/components/FieldFilterSelector/* (new reusable filter component)
  
  - **Screens**:
    - src/screens/Tally/Banner/index.jsx (updated with ChipValue and sort controls)
    - src/screens/Tally/TallyItem/index.jsx (updated with ChipValue)
    - src/screens/Tally/ChitHistory/index.jsx (updated with sorting, filtering, and ChipValue)
    - src/screens/Tally/ChitHistory/ChitHistoryHeader/index.jsx (updated with ChipValue)
    - src/screens/Tally/ChitDetail/index.jsx (updated with ChipValue and chain information)
    - src/screens/Tally/TallyCertificate/index.jsx (needs validation status indicators and improved organization)
    - src/screens/Tally/index.jsx (modified to use Redux sorting)
    - src/screens/Invite/index.jsx (updated with FieldFilterSelector)
  
  - **Redux**:
    - src/redux/chipCurrencySlice.js (enhanced error handling)
    - src/redux/chitHistoryFilterSlice.js (new slice for filter persistence) 
    - src/redux/tallySortSlice.js (new slice for home screen sorting)
    - src/redux/profileSlice.js (removed old filter implementation)
    - src/redux/reducers.js (updated to include new slices)
  
  - **Navigation**:
    - src/navigation/Navigator.jsx (removed obsolete FilterTallyScreen)

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

### Phase 3: Standardized Display Components
1. Create reusable component for displaying CHIP values
   - Style with underlined milliCHIPs for visual distinction
   - Support different sizes and contexts
   - Replace existing display patterns with the new component

2. Create reusable DigestResource component for files/images
   - Handle resources identified by digest checksums
   - Fetch from backend when needed or use cache
   - Cache in Redux store with optimized management
   - Support different resource types (images, documents, etc.)
   - Provide consistent display across all app screens
   - Handle multiple image contexts (avatars, IDs, documents)
   - Support various sizing and styling options (circle avatars, rectangular documents)
   - Optimize loading with placeholders and error states

## Pending Tasks

- [✅] Toggle ordering of chits in history view
- [✅] Make running balance display in chit history match the sort direction
- [✅] Add filtering options to Chit History (similar to home screen)
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
  - [✅] Store filter/sort preferences in Redux for persistence
  - [ ] Add date range filtering option
  - [ ] Review 'set' chit display presentation in ChitHistory
  - [ ] Consider disabling running balance display when filtered (future enhancement)
    - Running balance may be misleading if some chits are filtered out
    - Add visual indicator when balance doesn't represent full tally
  - [🔄] Retrofit existing filters to use FieldFilterSelector widget
    - [ ] Update Tally home screen filter to use FieldFilterSelector
    - [✅] Update Invite screen filter to use FieldFilterSelector
    - [ ] Evaluate other filter UI patterns for standardization
- [ ] Finish updating remaining components to use the ChipValue component
- [ ] Provide small and large variants of ChipValue for different screens
- [ ] Complete audit of manual unit conversion throughout the app
- [ ] Further improve visual hierarchy in tally list
- [ ] Clean up code by removing legacy currency conversion from parent components
- [ ] Enhance TallyCertificate screen with validation indicators and repair options
- [ ] Improve organization and visual hierarchy of certificate details

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
  - Sorting toggle for date (ascending/descending) using chit_date
  - Status filtering (default: 'good')
  - Chit type filtering (default: 'lift', 'tran')
  - Proper running balance calculation based on sort direction
- Extended ChipValue component to handle units directly
- Updated ChitHistory items to use ChipValue for running balance
- Created Redux-based filter persistence:
  - Added chitHistoryFilterSlice for ChitHistory filters
  - Replaced default filter screens with FieldFilterSelector
  - Updated WorkingTallies screen (Invite) with FieldFilterSelector
  - Safely removed obsolete Filter screen
- Implemented Home screen sorting enhancements:
  - Redesigned Home screen layout with better space utilization
  - Added three visual sorter controls (name, date, balance)
  - Created tallySortSlice for Redux-based sort state management
  - Implemented sorting by name (alphabetical asc/desc)
  - Implemented sorting by date (newest/oldest first)
  - Implemented sorting by balance (largest/smallest/absolute value)
  - Added visual indicators for active sorter
  - Connected sorting UI to data rendering
  - Removed obsolete FilterTallyList screen and related code
  - Cleaned up old sorting implementation in profileSlice.js
  - Removed obsolete language tags from database
  - Verified 'set' chit display works correctly in ChitHistory
  - Updated ChitDetail screen to use ChipValue component with proper styling
  - Added chain information display (chain_idx, chain_prev, chain_dgst) to ChitDetail screen

## Components to Update
- ✅ TallyItem component in home screen - COMPLETED
- ✅ Banner component for total display - COMPLETED 
- ✅ ChitHistory display - COMPLETED
  - Header complete
  - Items updated to use ChipValue
  - Running balance display improved and using ChipValue
- ✅ ChitDetail display - COMPLETED (ChipValue implementation)
  - [✅] Replace manual CHIP conversion with ChipValue component
  - [✅] Update net/amount display with ChipValue component
  - [✅] Remove section titles to simplify UI
  - [✅] Replace hardcoded button text with messageText references
    - [✅] "Refuse" button text → liftsPayMeText?.msg?.reject?.title
    - [✅] "Pay" button text → liftsPayMeText?.msg?.accept?.title
  - [✅] Add proper styling for ChipValue to match rest of screen
  - [✅] Add currency conversion display option (showCurrency=true)
  - [✅] **Added Chain Information:** Implemented display of chain_idx, chain_prev, chain_dgst as per tally_valid.md
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

## Home Screen Sorting Enhancement Plan

### Current Issues
- The "Tally Order" filter is hard-coded and uses a separate FilterTallyList screen
- Limited sorting capabilities (recent, ascending/descending balance, absolute balance, alphabetical)
- Space constraints in the current layout make it difficult to add more sorting options
- Inconsistent UI patterns between Home screen and ChitHistory screen

### Proposed Solution
1. **Layout Reorganization**
   - Move the Grand Total up next to the avatar and user name
   - Free up space for a row of sorter widgets
   - Design a more efficient use of space

2. **Sorting Controls Implementation**
   - Replace current filter with multiple sorting widgets using the same pattern as ChitHistory
   - Implement three independent sorters:
     1. **Name Sorter** (left): Sort alphabetically by partner name (ascending/descending)
     2. **Date Sorter** (middle): Sort by modification date (most/least recent)
     3. **Balance Sorter** (right): Sort by tally total (ascending/descending/absolute)

3. **Redux Integration**
   - Create a dedicated tallySortSlice for persisting sort preferences
   - Store individual sort states and active sorter
   - Ensure persistence across app sessions
   - Each sorter should toggle between ascending/descending states
   - Implement mechanisms for displaying the active sorter

4. **Implementation Checklist**
   - [✅] Redesign Home screen layout
     - [✅] Move Grand Total to header area next to avatar
     - [✅] Create space for sorter row
     - [✅] Reduce spacing between UI elements for better space utilization
     - [✅] Ensure responsive design on different screen sizes
   - [✅] Implement sorter components
     - [✅] Create Name Sorter widget (left)
     - [✅] Create Date Sorter widget (middle)
     - [✅] Create Balance Sorter widget (right)
     - [✅] Implement UI for indicating active sorter
     - [✅] Connect sorters to actual sorting functionality:
     - [✅] Name sorter should toggle between alphabetical ascending/descending
     - [✅] Date sorter should toggle between newest first/oldest first
     - [✅] Balance sorter should cycle through: largest positive first → smallest positive first → absolute value (magnitude)
   - [✅] Implement Redux integration
     - [✅] Create tallySortSlice for sort state with following structure:
       ```javascript
       {
         activeSorter: "name" | "date" | "balance", // Currently active sorter
         nameSort: {
           direction: "asc" | "desc",
           field: "part_cert", // Field to sort by
         },
         dateSort: {
           direction: "asc" | "desc",
           field: "tally_date", // Field to sort by
         },
         balanceSort: {
           direction: "asc" | "desc" | "abs", // abs = absolute value
           field: "net", // Field to sort by
         }
       }
       ```
     - [✅] Connect components to Redux
     - [✅] Migrate existing sort functionality
     - [✅] Create selectors for computed sorted data
   - [✅] Remove obsolete code
     - [✅] Clean up FilterTallyList screen
     - [✅] Update related navigation code
     - [✅] Remove old sorting implementation in profileSlice.js

5. **Technical Considerations**
   - Ensure compatibility with existing code
   - Maintain sorting performance for large tally lists
   - Consider tablet and smaller phone displays
   - Keep internationalization support for sort labels
   - Evaluate potential impacts on pull-to-refresh and FlatList performance
   
6. **Implementation Details**
   - Create a new file src/redux/tallySortSlice.js
   - Modify src/screens/Tally/Banner/index.jsx to use new sort widgets
   - Update the sorter icons to reflect current sort state:
     - Name sorter: sort-alpha-asc ↔ sort-alpha-desc
     - Date sorter: sort-amount-desc ↔ sort-amount-asc
     - Balance sorter: sort-numeric-desc → sort-numeric-asc → calculator (for absolute)
   - Highlight active sorter with different background color
   - Utilize existing sort functions but connect to new Redux state
   - Add action creators for toggling each sorter
   - Use useMemo for memoizing sorted results based on active sort criteria

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

- [✅] Improve filtering capabilities
  - [✅] Implement status filter using FieldFilterSelector
  - [✅] Implement chit type filter using FieldFilterSelector
  - [ ] Add date range filtering option
  - [ ] Add amount range filtering option

- [✅] Ensure consistent sorting implementation
  - [✅] Reuse Redux pattern for sort state management
  - [✅] Adapt sort utility functions to use chit_date
  - [✅] Implement persistent sorting preferences via Redux
  
- [✅] Code cleanup and optimization
  - [✅] Refactor ChipValue component to accept units parameter
  - [✅] Remove unused currency conversion code from parent components
  - [✅] Simplify ChipValue API by removing legacy props
  - [ ] Audit and optimize Redux selectors for performance
  - [ ] Add unit tests for currency conversion logic

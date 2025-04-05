# MyCHIPs Tally Components Dependency Analysis

## Introduction

This document analyzes the tally-related components in the MyCHIPs mobile application, their relationships, and their purposes. The analysis helps understand how different tally views relate to each other and what their purposes are, including component dependencies, props requirements, and state management.

## 1. Component Purposes and Functionality

### Main Tally Components

#### `Tally` (src/screens/Tally/index.jsx)
- **Purpose**: Main screen that displays a list of all open tallies.
- **Functionality**:
  - Fetches and displays a list of all open tallies
  - Provides sorting options (name, date, balance)
  - Shows tally summary with total net amount
  - Displays warning indicators for tallies with validity issues
  - Shows pending chit indicators
  - Opens payment modal when a tally is selected

#### `TallyItem` (src/screens/Tally/TallyItem/index.jsx)
- **Purpose**: Displays individual tally item in the list.
- **Functionality**:
  - Shows partner name and identification
  - Displays tally value in chips
  - Shows pending chit status if applicable
  - Displays validity warning indicator when needed
  - Retrieves validity status from Redux

#### `TallyHeader` (src/screens/Tally/TallyHeader/index.jsx)
- **Purpose**: Displays summary information at the top of tally list.
- **Functionality**:
  - Shows total net value across all tallies
  - Displays currency conversion
  - Provides search functionality
  - Shows pending transactions total

#### `OpenTallyView` (src/screens/Tally/OpenTallyView/index.jsx)
- **Purpose**: Screen container for viewing details of an open tally.
- **Functionality**:
  - Fetches complete tally data by tally_seq and tally_ent
  - Manages state for tally contracts and validity status
  - Integrates with Redux for validation status
  - Provides repair functionality through handleReSign and handleUpdateCert
  - Acts as a container that renders TallyEditView with proper props
  - Updates validity status from Redux during render
  
#### `TallyEditView` (src/screens/Tally/TallyEditView.jsx)
- **Purpose**: Core reusable component for viewing and editing tally details.
- **Functionality**:
  - Displays comprehensive tally information
  - Shows certificates and signatures with validity status
  - Provides repair functions for invalid certificates/signatures
  - Displays contract, comment, and trading variables
  - Controls editing capabilities based on tally state

#### `CertificateInformation` (src/screens/Tally/CertificateInformation.jsx)
- **Purpose**: Displays certificate details with validity status.
- **Functionality**:
  - Shows certificate holder name and chip address
  - Displays validity status indicator
  - Provides repair button when certificate is invalid
  - Opens detailed certificate view

#### `Banner` (src/screens/Tally/Banner/index.jsx)
- **Purpose**: Provides the top section of the Tally screen with user information and sorting controls.
- **Functionality**:
  - Displays user avatar and name
  - Shows total tally balance
  - Provides sorting options (name, date, balance)
  - Manages sort state through Redux

#### `TallyPreview` (src/screens/Tally/TallyPreview/index.jsx)
- **Purpose**: Main container for previewing and editing a draft tally before sharing or offering.
- **Functionality**:
  - Manages tally data fetching and updates
  - Provides certificate updates and contract selection
  - Renders different action buttons based on tally state (share, offer, accept)
  - Handles form state and submission

#### `ChitHistory` (src/screens/Tally/ChitHistory/index.jsx)
- **Purpose**: Displays the transaction history for a specific tally.
- **Functionality**:
  - Fetches and displays chit (transaction) history
  - Provides sorting and filtering options
  - Shows running balance calculations
  - Supports detailed viewing of individual chits

#### `GenerateKeysDialog` (src/screens/Tally/TallyPreview/GenerateKeysDialog/index.jsx)
- **Purpose**: Modal dialog for generating cryptographic keys required for tallies.
- **Functionality**:
  - Generates ECDSA key pairs for signing tallies
  - Stores keys securely using keychain storage
  - Updates user's public key on the server

#### `PendingChits` (src/screens/Tally/PendingChits/index.jsx)
- **Purpose**: Displays and manages pending transaction requests.
- **Functionality**:
  - Shows list of pending chits requiring action
  - Provides accept/reject functionality for chits
  - Fetches chit data and refreshes on changes

### TallyReview Components

#### `TallyReviewView` (src/screens/TallyReview/TallyReviewView.jsx)
- **Purpose**: Visual representation of tally relationships and limits.
- **Functionality**:
  - Visually represents the foil/stock relationship
  - Shows graphical representation of credit/risk relationship
  - Allows editing of tally limits
  - Provides a switch button to toggle tally type

### Utility Files

#### `tally-verification.js` (src/utils/tally-verification.js)
- **Purpose**: Provides functions for validating tally cryptographic integrity.
- **Functionality**:
  - Verifies tally signatures
  - Checks if public keys match
  - Determines validity status
  - Enhances tallies with validity information

#### `tally-repair.js` (src/utils/tally-repair.js)
- **Purpose**: Utility functions for repairing invalid tallies.
- **Functionality**:
  - Provides functions to re-sign tallies
  - Facilitates certificate updates
  - Handles user confirmation and authentication
  - Communicates with backend for repairs

## 2. Hierarchical Dependency Map

```
Tally (screens/Tally/index.jsx)
├── Banner
│   ├── Avatar
│   └── Sorting controls
├── TallyHeader
├── TallyItem
│   ├── Avatar
│   ├── ChipValue
│   ├── Warning_16 (SvgAssets)
│   └── useMessageText (hook)
└── PayModal (screens/Pay)

OpenTallyView (screens/Tally/OpenTallyView/index.jsx)
├── useSocket (hook)
├── Redux
│   ├── updateValidity (from updateTallySlice)
│   └── validityStatuses (selector)
├── tally-repair.js
│   ├── repairTallySignature
│   └── repairTallyCertificate
└── TallyEditView

TallyPreview (screens/Tally/TallyPreview/index.jsx)
├── useSocket (hook)
├── GenerateKeysDialog
├── UpdateHoldCert
└── TallyEditView

ChitHistory (screens/Tally/ChitHistory/index.jsx)
├── ChitHistoryHeader
├── ChitItems
└── Filter controls

PendingChits (screens/Tally/PendingChits/index.jsx)
├── Header
├── ChitItem
│   ├── Detail
│   ├── AcceptButton
│   └── RejectButton
└── ChitTypeText

TallyReviewView (screens/TallyReview/TallyReviewView.jsx)
├── Avatar
├── HelpText
├── SvgAssets (icons)
└── IconTooltip

TallyEditView (screens/Tally/TallyEditView.jsx)
├── HelpText
├── TallyReviewView
├── CertificateInformation
│   ├── HelpText
│   ├── ValidityIcon
│   └── useMessageText (hook)
├── ValidityIcon
└── FontAwesome (icons)

Redux Store
├── openTalliesSlice
│   └── updateTallyValidityStatuses
└── updateTallySlice
    ├── setValidityStatus
    └── updateValidity

Utils
├── tally-verification.js
│   ├── verifyTallySignature
│   ├── checkKeyMatch
│   └── getTallyValidityStatus
└── tally-repair.js
    ├── repairTallySignature
    └── repairTallyCertificate

Services
└── tally.js
    ├── fetchTallies
    ├── reassertCertificate
    ├── reassertSignature
    └── Various other tally operations
```

## 3. Tally View Types

The MyCHIPs app provides several different ways to view and interact with tallies:

### 1. Tally List View
- **Component**: `Tally` (index.jsx)
- **Purpose**: Shows all open tallies in a list format
- **Features**:
  - Sorting by name, date, or balance
  - Search functionality
  - Summary of total tally value
  - Quick indicators for validity and pending chits

### 2. Tally Detail View
- **Component**: `OpenTallyView` (container) with `TallyEditView` (presentation)
- **Purpose**: Comprehensive view of a single tally
- **Features**:
  - Certificate and signature details with validity status
  - Contract information
  - Trading variables
  - Comments and metadata
  - Repair options for invalid tallies

### 3. Tally Review View
- **Component**: `TallyReviewView`
- **Purpose**: Visual representation of tally relationship
- **Features**:
  - Graphical representation of foil/stock relationship
  - Credit/risk visualization
  - Limit editing interface
  - Tally type switching

### 4. Tally Certificate View
- **Component**: Accessed through `CertificateInformation`
- **Purpose**: Detailed view of certificates
- **Features**:
  - Full certificate details
  - Accessed via navigation to `TallyCertificate` screen

## 4. Component Props and State Management

### Tally (Main Screen)
- **Props**:
  - `navigation`: For navigating between screens
- **State Management**:
  - `tallies`: List of all open tallies (from Redux)
  - `filteredTallies`: Tallies filtered by search
  - `sortedTallies`: Tallies sorted by criteria
  - `tally`: Selected tally for payment modal
  - `isVisible`: Controls payment modal visibility
  - `conversionRate`: Currency conversion rate
  
### OpenTallyView (Tally Detail Container)
- **Props**:
  - `route.params`: Contains tally_seq and tally_ent for fetching the tally
  - `navigation`: For navigating between screens
- **State Management**:
  - `tally`: Complete tally object fetched from the backend
  - `loading`: Loading state during fetch operations
  - `tallyContracts`: Available contracts for tallies
- **Redux State Used**:
  - `validityStatuses`: Map of validity statuses indexed by tally_uuid
- **Functions**:
  - `fetchTally`: Fetches tally data with all required fields
  - `handleReSign`: Handles re-signing the tally with current key
  - `handleUpdateCert`: Handles updating certificate with current key

### TallyItem
- **Props**:
  - `tally`: Tally object with complete data
  - `image`: Partner avatar image
  - `conversionRate`: Currency conversion rate
  - `currency`: Preferred currency code
- **Redux State Used**:
  - `validityStatuses`: Map of validity statuses indexed by tally_uuid

### TallyEditView
- **Props**:
  - `tally`: Complete tally object
  - `tallyType`: 'foil' or 'stock'
  - `contract`: Contract ID
  - `holdTerms`: Holder's terms
  - `partTerms`: Partner's terms
  - `comment`: Tally comment
  - `setComment`: Function to update comment
  - `onHoldTermsChange`: Function to update holder terms
  - `onPartTermsChange`: Function to update partner terms
  - `setTallyType`: Function to toggle tally type
  - `setContract`: Function to update contract
  - `tallyContracts`: Available contract options
  - `onReSign`: Function to re-sign the tally
  - `onUpdateCert`: Function to update the certificate
  - `navigation`: For navigating to certificate view
- **Redux State Used**:
  - `validityStatuses`: Map of validity statuses indexed by tally_uuid

### CertificateInformation
- **Props**:
  - `title`: Certificate title
  - `name`: Certificate holder name
  - `chipAddress`: CHIP address (cuid:agent)
  - `onViewDetails`: Function to view certificate details
  - `certText`: Message text for certificate fields
  - `validityStatus`: Validity status string
  - `onRepair`: Optional function for certificate repair

### TallyReviewView
- **Props**:
  - `partCert`: Partner certificate
  - `holdCert`: Holder certificate
  - `tallyType`: 'foil' or 'stock'
  - `setTallyType`: Function to toggle tally type
  - `partTerms`: Partner's terms
  - `holdTerms`: Holder's terms
  - `onHoldTermsChange`: Function to update holder terms
  - `onPartTermsChange`: Function to update partner terms
  - `canEdit`: Boolean to control editing capability
- **Redux State Used**:
  - `imagesByDigest`: Map of avatar images indexed by digest

## 5. Tally Validation System

### Validation Process
1. When tallies are fetched in `openTalliesSlice.js`:
   - Basic tally data is returned immediately for UI display
   - Validation is performed asynchronously in the background
   - Results are dispatched to both `openTalliesSlice` and `updateTallySlice`

2. The `tally-verification.js` utility provides core functions:
   - `verifyTallySignature`: Checks cryptographic validity
   - `checkKeyMatch`: Verifies if the tally's key matches the user's current key
   - `getTallyValidityStatus`: Determines the overall validity status

3. Validity statuses are stored in:
   - `openTalliesSlice`: For immediate UI updates
   - `updateTallySlice`: For centralized validity state management

### Repair System
1. The `tally-repair.js` utility provides repair functions:
   - `repairTallySignature`: Re-signs a tally with the current key
   - `repairTallyCertificate`: Updates the certificate with current key

2. The repair process:
   - Requires biometric authentication
   - Uses backend procedures via `reassertCertificate` and `reassertSignature`
   - Follows fire-and-forget pattern with toast notifications

## 6. Key Insights

1. **Separation of Concerns**:
   - View components focus on presentation
   - Redux handles state management
   - Utility files handle validation and repair logic
   - Services handle API interactions

2. **Validation Architecture**:
   - Asynchronous validation that doesn't block UI rendering
   - Central store for validity statuses
   - Multiple validity states: valid, warning, invalid

3. **Component Reuse**:
   - `TallyEditView` serves as the core component for various tally views
   - `CertificateInformation` encapsulates certificate display and validation
   - `ValidityIcon` provides consistent validity indication

4. **Security Considerations**:
   - Biometric authentication for sensitive operations
   - Confirmation dialogs for irreversible actions
   - Clear warnings about implications of repair actions

## 7. Planned Improvements

Based on the analysis of the codebase and issues, several improvements are planned:

1. **UI Enhancements**:
   - Add tooltips to warning indicators
   - Make validation indicators consistent across all tally views
   - Improve certificate and signature display

2. **Functional Improvements**:
   - Add dependency validation between certificates and signatures
   - Implement a "Fix All" approach for invalid tallies
   - Add chit validation and chain verification

3. **Documentation and Testing**:
   - Add unit tests for validation functions
   - Test with different tally scenarios
   - Improve documentation of the validation system

## 8. Navigation Pathways to Tally Screens

This section documents the various ways users can navigate to each tally-related screen.

### Tally List (Main Screen)
- **Home Navigation Tab**: Click on the Home tab in the bottom navigation
- **Deep Link**: `mychips://tally-list` 

### OpenTallyView (Tally Detail)
- **From Tally List**: Click on any open tally in the tally list
- **Deep Link**: `mychips://tally-view/{tally_seq}` 
- **From Notifications**: Clicking on a tally-related notification

### TallyPreview
- **From Draft Tallies**: Click on any draft tally in the tally list
- **From Invite Screen**: After creating a new tally draft
- **Deep Link**: `mychips://tally-preview/{tally_seq}`

### ChitHistory
- **From Tally Detail**: Click on "Transaction History" section in tally details
- **From Activity Screen**: Click on a transaction item related to a specific tally

### PendingChits
- **From Tally Detail**: Clicking on pending transactions indicator
- **From Notifications**: Clicking on a pending chit notification
- **From Activity Screen**: Filter for pending transactions

### TallyReview
- **When Creating Tally**: As part of the tally creation flow
- **When Editing Draft**: Accessing a draft tally for editing

### TallyCertificate
- **From Certificate Information**: Click on any certificate display component
- **From Key Management**: View existing certificates associated with tallies

### TallyContract
- **From Tally Detail**: Click on the "eye" icon next to the contract section
- **From Tally Preview**: When viewing or selecting a contract for a draft tally
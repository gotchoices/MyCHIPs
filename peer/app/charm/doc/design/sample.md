# User Story: Daily Wallet Management

## Story Overview

**As a** MyCHIPs user  
**I want to** quickly see my current CHIP balance and recent transaction activity  
**So that** I can understand my spending power and financial activity at a glance  

## Acceptance Criteria

- [ ] I can see my current CHIP balance prominently displayed
- [ ] I can view my 3-5 most recent transactions with key details
- [ ] I can access quick actions for common tasks (send, request, QR code)
- [ ] I can navigate to detailed transaction history
- [ ] The interface updates in real-time when new transactions occur
- [ ] All information is accessible without additional authentication once logged in

## Screen Purpose

The Wallet Overview screen serves as the primary landing page for the MyCHIPs mobile application. It provides users with:

1. **Immediate balance visibility** - Users can see their available CHIP balance prominently displayed
2. **Quick action access** - Common tasks like sending money, requesting payment, and sharing QR codes are one tap away
3. **Recent activity context** - The most recent transactions provide immediate context about spending and receiving patterns
4. **Navigation hub** - The bottom tab bar provides access to all major app sections

## Design Rationale

### Visual Hierarchy
- **CHIP Balance Card** is the primary focal point, using a prominent green color that aligns with the currency's positive nature
- **Quick Actions** are secondary but easily discoverable, using familiar iconography
- **Recent Transactions** provide context without overwhelming the primary information

### Interaction Patterns
- Follows iOS Human Interface Guidelines for navigation and layout
- Uses standard iOS patterns (tab bars, navigation headers, cards)
- Maintains consistency with Apple Pay and other financial apps users are familiar with

### Accessibility Considerations
- High contrast text ensures readability
- Standard touch targets (44pt minimum) for all interactive elements
- Clear visual hierarchy supports screen readers
- Color is not the only indicator of status (text labels accompany colored elements)

## Screen Design

The following wireframe demonstrates how this user story is implemented in the wallet overview interface:

![Wallet Overview Screen](../images/wallet-overview.svg)

*Generated from: [wallet-overview.xml](../screens/wallet-overview.xml)*

## Semantic Component Approach

This screen demonstrates our new **semantic, data-driven component system** designed for rapid prototyping and AI-powered React Native conversion.

### Key Features

**🎯 Semantic Markup**: Each element uses meaningful tag names like `<balance-card>`, `<transaction-item>`, `<quick-action-card>`

**📊 Data-Driven**: All content and styling passed via data attributes:
```svg
<transaction-item
  data-name="Coffee Shop"
  data-description="Payment sent"
  data-time="Today, 2:30 PM"
  data-amount="-¢8.50"
  data-amount-color="#FF3B30"
  data-icon="☕"
  data-avatar-color="#FF9500"/>
```

**🤖 AI-Parseable**: Clear structure maps directly to React Native components:
```tsx
<TransactionItem
  name="Coffee Shop"
  description="Payment sent"
  time="Today, 2:30 PM"
  amount="-¢8.50"
  amountColor="#FF3B30"
  icon="☕"
  avatarColor="#FF9500"
/>
```

### Component Categories

#### **Layout Widgets**
- `<app-header>` - Screen header with title and navigation
- `<bottom-tab-bar>` - Bottom navigation with tab items
- `<section-header>` - Section title headers

#### **Content Widgets**
- `<balance-card>` - Primary balance display with branding
- `<transaction-item>` - Individual transaction list items
- `<quick-action-card>` - Action buttons in grid layout

#### **Interactive Widgets**
- `<action-button-primary>` - Primary call-to-action buttons
- `<action-button-secondary>` - Secondary action buttons
- `<tab-item>` - Navigation tab with active/inactive states

### Advantages Over Previous Approach

| Traditional SVG | Semantic Approach |
|----------------|-------------------|
| `<rect>`, `<circle>`, `<text>` | `<transaction-item>`, `<balance-card>` |
| Hardcoded styling | Data-driven parameters |
| 75+ lines per screen | 25+ lines per screen |
| Hard to parse by AI | Direct React Native mapping |
| Manual positioning | Semantic layout structure |

## Technical Implementation Notes

### Semantic Component Architecture

**Component Definition**: All widgets defined in `svg/semantic-components.svg` with placeholder tokens:
```svg
<g id="transaction-item">
  <text>[NAME]</text>
  <text>[DESCRIPTION]</text>
  <text fill="[AMOUNT_COLOR]">[AMOUNT]</text>
</g>
```

**Screen Usage**: Semantic tags with data attributes:
```svg
<transaction-item 
  data-name="Coffee Shop"
  data-description="Payment sent"
  data-amount-color="#FF3B30"/>
```

**AI Processing**: Direct mapping to React Native:
```tsx
// AI can automatically generate:
<TransactionItem
  name="Coffee Shop"
  description="Payment sent"
  amountColor="#FF3B30"
/>
```

### Benefits for AI Conversion

1. **Semantic Structure** - Clear component hierarchy and relationships
2. **Data Separation** - Content separated from presentation logic  
3. **Consistent Patterns** - Predictable data attribute naming conventions
4. **Type Safety** - Data attributes indicate expected prop types
5. **Layout Context** - Positioning and grouping preserved semantically

### Data Flow
- Balance data fetched from MyCHIPs engine
- Transaction history loaded incrementally (latest 3-5 shown)
- Real-time updates for new transactions via WebSocket connection
- Offline-first design with cached balance and transaction data

## User Interactions

### Primary Actions
1. **Send Money** - Navigate to payment flow
2. **Request Payment** - Generate payment request
3. **QR Code** - Display user's payment QR code
4. **Transaction Details** - Tap any transaction for full details

### Navigation
- **Tab Navigation** - Switch between major app sections
- **Transaction History** - "See All" button leads to complete transaction list
- **Settings Access** - Available via bottom tab bar

## Success Metrics

### Usability Metrics
- Time to understand current balance (target: <2 seconds)
- Success rate for initiating payments (target: >90%)
- User satisfaction with information hierarchy (target: >4.5/5)

### Business Metrics
- Daily active users viewing balance
- Conversion rate from overview to payment actions
- Frequency of transaction history viewing

## Accessibility Features

### Screen Reader Support
- Semantic labels for all interactive elements
- Balance announced as "One thousand two hundred forty-seven dollars and fifty cents in CHIPs"
- Transaction items include complete context ("Payment sent to Coffee Shop for eight dollars and fifty cents, today at 2:30 PM")

### Visual Accessibility
- Minimum 4.5:1 color contrast ratio maintained
- Text scales with system font size preferences
- Color-blind friendly design (status not dependent on color alone)

### Motor Accessibility
- Minimum 44pt touch targets
- Adequate spacing between interactive elements
- Support for VoiceOver and Switch Control

## Future Enhancements

### Phase 2 Features
- Pull-to-refresh for transaction updates
- Biometric authentication for balance viewing
- Customizable quick action buttons
- Balance trend visualization

### Phase 3 Features
- Multiple currency support
- Spending category breakdown
- Budget tracking integration
- Social payment features

## Development Notes

### Performance Considerations
- Virtual scrolling for large transaction lists
- Image optimization for user avatars
- Background sync for transaction updates
- Cached balance display for immediate app startup

### Security Requirements
- Balance data encrypted at rest
- Transaction details require authentication to view
- Automatic session timeout after inactivity
- Secure WebSocket connections for real-time updates

---

*This design specification serves as the source of truth for implementing the Wallet Overview screen. All changes should be reflected in both this document and the corresponding SVG wireframes.*

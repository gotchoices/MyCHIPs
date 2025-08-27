# Home Dashboard Design Specifications

*Human-authored design requirements for `screens/home-dashboard.xml`*

## Layout Requirements

### Balance Display
- **Grand total** prominently displayed at top showing combined CHIP balance
- Show both CHIP amount (₡) and USD equivalent 
- Include context help icon for CHIP balance explanation

### Tally List
- **Scrollable container** for list of tally relationships
- Each tally item shows:
  - Partner name/identifier
  - Current balance in CHIPs (positive/negative with color coding)
  - USD equivalent amount
  - Tally status indicator (active, pending, suspended)
- **Zero state**: "No tallies yet" message with "Find Partners" call-to-action button

### Navigation & Actions
- Getting started section for new users (when tally list is empty)
- Quick action shortcuts (invite partners, scan QR, etc.)
- Bottom tab bar always visible
- Context helps throughout for MyCHIPs concepts

## Interaction Requirements

- **Tap tally item** → navigate to tally detail/management screen
- **Pull-to-refresh** on tally list to update balances
- **Context help taps** → open educational content
- **Getting started item taps** → navigate to relevant setup flows

## Data Requirements

- **Real-time balance updates** when transactions occur
- **Currency conversion** CHIP ↔ USD using current rates
- **Tally partner status** (online, last seen, verification level)
- **Transaction preview** (most recent activity per tally)

## Visual Hierarchy

1. **Primary**: Grand total balance (largest, most prominent)
2. **Secondary**: Individual tally balances 
3. **Tertiary**: USD equivalents, status indicators, metadata
4. **Supporting**: Help icons, empty states, navigation

## Notes

- This screen serves as the main hub - users return here frequently
- Must work well with zero tallies (new users) and many tallies (active users)
- Balance visibility is primary user need - make it immediately clear

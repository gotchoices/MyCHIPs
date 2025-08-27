# Tally Review Design Specifications

*Human-authored design requirements for `screens/tally-review.xml`*

## Layout Requirements

### Credit Limit Section
- **Dual credit limit inputs**: User trusts Partner (CHIPs), Partner trusts User (CHIPs)
- Show **both CHIP and USD equivalents** for each amount
- **Color coding**: Green for positive credit, red for negative, neutral for zero
- **Context help icons** explaining credit risk and trust concepts

### Identity Information Section  
- **User identity display**: Name, email, phone (from onboarding)
- **Optional fields**: Address, birthdate, Tax ID (greyed out unless required)
- **Document attachments** area for identity verification
- **Edit capability** for adding more information as needed

### Contract & Terms Section
- **Contract selector**: Dropdown showing available tally contracts (default: MyCHIPs.org 1.0)
- **View contract button**: Opens PDF viewer with full contract text
- **Share contract**: Allow sharing contract for legal review
- **Comment field**: Free text for personal message to partner

### Advanced Options (Collapsible)
- **Trading variables**: Advanced tally parameters with context help
- **Expiration settings**: Token expiration time (default 24 hours)
- **Notification preferences**: How to handle tally events

## Interaction Requirements

### Input Validation
- **Real-time validation** on credit limit fields
- **Currency conversion** display as user types amounts
- **Required field indicators** and validation messages
- **Save/Cancel** state management

### Progressive Disclosure
- **Basic view**: Credit limits, identity, comment only
- **Advanced checkbox**: Reveals trading variables and technical settings
- **Context help expansion**: Detailed explanations without leaving screen

### State Management
- **Draft saving**: Auto-save form data as user works
- **Template creation**: Option to save current settings as reusable template
- **Negotiation states**: Accept/Reject/Counter buttons based on context

## Data Requirements

### Display States
- **Creation mode**: User is creating new tally invitation
- **Response mode**: User is responding to received invitation  
- **Negotiation mode**: Back-and-forth counter-offers
- **Read-only mode**: Finalized tally review

### Real-time Updates
- **Currency conversion**: CHIP ↔ USD using current rates
- **Partner status**: Online/offline, last seen
- **Negotiation progress**: Current offer state, who's turn to respond

## Visual Hierarchy

1. **Primary**: Credit limit amounts (largest, most prominent)
2. **Secondary**: Identity information, contract selection
3. **Tertiary**: Comments, advanced options
4. **Supporting**: Help icons, validation messages, action buttons

## Notes

- This screen serves multiple purposes: creation, response, negotiation, review
- Must handle both symmetric (mutual credit) and asymmetric (one-way credit) scenarios
- Context help is critical - users need education about trust and credit concepts
- Template system reduces friction for repeat tally creation

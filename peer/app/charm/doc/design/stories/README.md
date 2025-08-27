# User Stories

This directory contains user stories that describe how people discover, onboard, and use the MyCHIPs mobile application.

## Story Structure

Each story file follows this template with a **clear boundary line**:

### Human-Authored Sections (Above the Line)
- **Story Overview** - Who, what, why in user story format (includes context)
- **Sequence** - Step-by-step flow (the core content you fill in)
- **Acceptance Criteria** - What success looks like (business requirements)

**`---` (Boundary Line)**

### AI-Generated Sections (Below the Line)
- **Scenarios** - Detailed narratives with screen references
- **Related Journeys** - Links to other relevant stories

## Onboarding Stories

### [Discovery-Driven Onboarding](onboarding-discovery.md)
User learns about MyCHIPs through media/marketing and explores the app voluntarily.

**Key Flow**: Podcast/website → app store → download → explore → setup

### [Payment Urgency Onboarding](onboarding-payment-urgency.md) 
User needs to pay a merchant who accepts MyCHIPs and must set up account quickly.

**Key Flow**: Point of sale → QR scan → app install → quick setup → payment

### [Merchant Setup Onboarding](onboarding-merchant-setup.md)
User needs to receive payment and must set up account to accept MyCHIPs.

**Key Flow**: Customer request → app install → account setup → generate QR → receive payment

### [Email Invitation Onboarding](onboarding-email-invitation.md)
User receives payment request or invoice link via email and follows it to complete payment.

**Key Flow**: Email notification → click link → app install → payment context → complete transaction

## Usage Stories

### [First Friend Tally](first-friend-tally.md)
User who completed discovery invites a trusted friend to form their first tally relationship.

**Key Flow**: Post-discovery → friend conversation → invitation → mutual setup → tally negotiation → active relationship

## Writing Guidelines

### For the Sequence Section
- Write as numbered steps in plain language
- Focus on user actions and system responses
- Include decision points and alternative paths
- Don't worry about screen details - just the flow
- Keep it concise but complete

### Example Sequence
```
1. User hears about MyCHIPs on podcast
2. User visits mychips.org to learn more
3. User clicks "Download App" button
4. User installs app from app store
5. User opens app and sees welcome screen
6. User taps "Get Started" 
7. System guides user through account creation
8. User verifies phone number
9. User sets up security (PIN/biometric)
10. User sees main wallet with $0 balance
11. User explores help/tutorial content
```

## Next Steps

1. **Fill in Sequences** - Complete the step-by-step flows in each story
2. **Design Screens** - Create XML screen definitions for key steps
3. **Build Wireframes** - Generate SVG visualizations
4. **AI Enhancement** - Let AI fill in detailed scenarios with screen references
5. **Validation** - Review complete user journeys for gaps and issues

# MyCHIPs Mobile App - Design Specification

*Master design document for the MyCHIPs peer-to-peer credit system mobile application*

## 📖 Completed User Stories

### Onboarding & Tally Creation
- [**Discovery-Driven Onboarding**](stories/onboarding-discovery.md) - User learns about MyCHIPs and explores the app ✅ *Complete with scenarios*
- [**First Friend Tally**](stories/first-friend-tally.md) - Setting up the first tally relationship with a trusted partner ✅ *Complete with scenarios*  
- [**Email Tally Response**](stories/onboarding-email-tally.md) - Responding to a tally invitation received via email ✅ *Complete with scenarios*

### Template Stories (Human Sequences Needed)
- [**Payment Urgency Onboarding**](stories/onboarding-payment-urgency.md) - User needs to pay at point of sale
- [**Merchant Setup Onboarding**](stories/onboarding-merchant-setup.md) - Business owner accepting CHIPs
- [**Email Invoice Payment**](stories/onboarding-email-invoice.md) - Paying an invoice via email link

*See [STATUS.md](STATUS.md) for complete development status and future story ideas.*

## 📱 Screen Designs

### Onboarding Flow
- [**App Launch**](images/app-launch.svg) - Welcome screen with MyCHIPs introduction ([source](screens/app-launch.xml))
- [**Identity Setup**](images/identity-setup.svg) - Basic user information collection ([source](screens/identity-setup.xml))

### Main Interface  
- [**Home Dashboard**](images/home-dashboard.svg) - Main wallet with balance and getting started guidance ([source](screens/home-dashboard.xml))
- [**Marketplace**](images/marketplace.svg) - Browse vendors accepting CHIPs ([source](screens/marketplace.xml))

### Tally Management
- [**Tally Review**](images/tally-review.svg) - Create, review, and negotiate tally relationships ([source](screens/tally-review.xml))
- [**QR Share**](images/qr-share.svg) - Share tally invitations via QR code ([source](screens/qr-share.xml))
- [**Tally Templates**](images/tally-templates.svg) - Manage reusable tally configurations ([source](screens/tally-templates.xml))

### Legacy/Example Screens
- [**Wallet Overview**](images/wallet-overview.svg) - Earlier wallet concept ([source](screens/wallet-overview.xml))

## 🎨 Design System

### Navigation System
- [**Navigation Tree**](navigation/sitemap.md) - Complete 5-tab navigation structure
- [**Global Specifications**](navigation/global-specs.md) - Tab bar, breadcrumbs, and universal patterns
- [**Deep Link Routing**](navigation/deep-links.md) - URL patterns and routing specifications

### Component Library
- [**XSLT Component Transforms**](components/transforms/master.xsl) - Semantic XML → SVG transformation system
- [**Design Specifications**](specs/) - Human-authored requirements for complex screens

### Technical Implementation
- [**Build System**](README.md#build-system) - XML to SVG wireframe generation
- [**Screen Authoring**](screens/README.md) - Guidelines for creating semantic screen designs

## 📋 Current Status

### ✅ Completed (Ready for React Native Implementation)
- **3 complete user stories** with human sequences + AI scenarios + screen references
- **7 screen designs** with semantic XML source and SVG wireframes  
- **Component library** with 20+ reusable UI components
- **Build system** for automated wireframe generation
- **Design specifications** for complex screen requirements

### 🚧 In Progress
- **3 onboarding story templates** waiting for human sequence completion
- **Screen iteration** based on new story requirements
- **Component expansion** for payment and transaction flows

*See [STATUS.md](STATUS.md) for detailed development checklist and future roadmap.*

## 🚀 Getting Started

### For Story Writers
1. Review [completed stories](stories/) to understand the format
2. Use [story templates](stories/) to write new user sequences  
3. Follow [writing guidelines](stories/README.md) for human vs. AI sections

### For Screen Designers  
1. Check existing [design specs](specs/) for requirements
2. Follow [screen authoring guidelines](screens/README.md)
3. Use the [build system](README.md#quick-start) to generate SVG wireframes
4. Reference [component library](components/transforms/master.xsl) for available elements

### For Developers
1. Review [screen designs](images/) for implementation requirements
2. Study [component transforms](components/transforms/master.xsl) for React Native mapping
3. Use semantic XML as component structure guide
4. Follow data attribute patterns for component props

### For AI Code Generation
1. Parse [user story scenarios](stories/) for behavior requirements
2. Read [design specifications](specs/) for layout and interaction details  
3. Use [screen XML](screens/) as semantic component structure
4. Reference [SVG wireframes](images/) for visual validation

---

*This design specification documents the completed foundation for MyCHIPs mobile app development. All user stories, screen designs, and technical specifications are production-ready.*

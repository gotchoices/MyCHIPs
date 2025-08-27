# MyCHIPs Mobile App Design System

This directory contains the complete UI/UX design specifications for the MyCHIPs mobile application, from user stories through to implementation-ready screen designs.

## 📁 Directory Structure

```
design/
├── README.md                    # This file - overview and build instructions
├── index.md                     # Master design document with navigation tree
├── build.sh                     # Build script for XML → SVG transformation
├── package.json                 # Node.js dependencies for build tools
│
├── stories/                     # User stories and usage patterns
│   ├── README.md               # Story writing guidelines
│   ├── 01-onboarding.md        # New user registration and setup
│   ├── 02-daily-usage.md       # Common daily operations
│   ├── 03-peer-interactions.md # Sending/receiving payments
│   ├── 04-merchant-payments.md # Business transactions
│   ├── 05-account-management.md# Settings, security, history
│   └── 99-edge-cases.md        # Error handling, offline scenarios
│
├── navigation/                  # App navigation structure
│   ├── sitemap.md              # Complete navigation tree
│   ├── user-flows.md           # Key user journey flows
│   └── wireframes/             # Navigation wireframes
│       ├── tab-structure.xml
│       ├── modal-flows.xml
│       └── deep-linking.xml
│
├── screens/                     # Screen designs (XML source → SVG output)
│   ├── README.md               # Screen authoring guidelines
│   ├── auth-login.xml          # Login screen definition
│   ├── auth-register.xml       # Registration screen
│   ├── wallet-overview.xml     # Main wallet dashboard
│   ├── wallet-send.xml         # Send money flow
│   ├── pay-scan-qr.xml         # QR code scanner
│   ├── history-list.xml        # Transaction history
│   ├── settings-profile.xml    # User profile settings
│   └── ... (other screens)
│
├── images/                     # Generated wireframes (build output)
│   ├── auth-login.svg          # Rendered wireframes
│   ├── auth-register.svg       # (referenced by documentation)
│   ├── wallet-overview.svg
│   ├── wallet-send.svg
│   └── ... (mirrors screens/)
│
├── components/                  # Reusable UI component system
│   ├── README.md               # Component authoring guidelines
│   ├── transforms/             # XSLT transformation templates
│   │   ├── layout.xsl          # Headers, navigation, containers
│   │   ├── forms.xsl           # Inputs, buttons, validation
│   │   ├── cards.xsl           # Balance cards, info cards
│   │   ├── lists.xsl           # Transaction lists, menu lists
│   │   ├── modals.xsl          # Dialogs, alerts, overlays
│   │   └── master.xsl          # Main transform that imports all others
│   │
│   ├── theme/                  # Design system definitions
│   │   ├── colors.xml          # Color palette and semantic colors
│   │   ├── typography.xml      # Font scales, weights, styles
│   │   ├── spacing.xml         # Margins, padding, layout grids
│   │   ├── shadows.xml         # Elevation and shadow definitions
│   │   └── breakpoints.xml     # Responsive design breakpoints
│   │
│   └── icons/                  # Icon system
│       ├── system.xml          # iOS system icons
│       ├── brand.xml           # MyCHIPs branded icons
│       └── custom.xml          # Custom app-specific icons
│
├── assets/                      # Supporting design assets
│   ├── images/                 # Screenshots, photos, illustrations
│   ├── fonts/                  # Custom fonts (if any)
│   └── brand/                  # Logos, brand assets
│
└── exports/                     # Output for development handoff
    ├── react-native/           # RN component specifications
    ├── figma/                  # Figma import files
    └── specs/                  # Developer specification docs
```

## 🚀 Quick Start

### Prerequisites
```bash
# Only system dependencies needed
# macOS: brew install libxslt
# Linux: apt-get install xsltproc
# Windows: Use WSL or install libxslt
```

### Build All Screens
```bash
# Build all XML screens to SVG
./build.sh

# Or build specific categories
./build.sh wallet
./build.sh auth
```

### View Designs
```bash
# Start local preview server (Python)
python3 -m http.server 3000

# Or use any static server
# Open browser to http://localhost:3000
```

## 📝 Workflow

### 1. **User Stories** (`stories/`)
Write comprehensive user stories covering all usage patterns:
- What users want to accomplish
- Steps they take to get there
- Error conditions and edge cases
- Success criteria and validation

### 2. **Navigation Design** (`navigation/`)
Design the overall app structure:
- Tab bar organization
- Modal flows and deep linking
- Back button behavior
- Navigation state management

### 3. **Screen Design** (`screens/source/`)
Create individual screen layouts:
- Author in clean XML with semantic components
- Build generates SVG for visual review
- Link screens together in user flows

### 4. **Component System** (`components/`)
Maintain the reusable design system:
- Update transforms when adding new component types
- Keep theme definitions centralized
- Document component usage patterns

### 5. **Documentation** (`index.md`, story files)
Link everything together:
- Master index shows complete app structure
- Stories reference relevant screens
- Screens reference supporting components

## 🔧 Build System

The build system transforms semantic XML screen definitions into visual SVG wireframes:

### XML Input (Semantic)
```xml
<wallet-screen>
    <balance-card data-amount="¢1,247.50"/>
    <transaction-item data-name="Coffee Shop" data-amount="-¢8.50"/>
</wallet-screen>
```

### SVG Output (Visual)
```svg
<svg width="375" height="812">
    <!-- Fully rendered visual wireframe -->
</svg>
```

### Component Transforms
Each component type has its own XSLT template that defines how semantic markup becomes visual SVG.

## 📋 File Naming Conventions

- **Stories**: `##-description.md` (numbered for reading order)
- **Screens**: `kebab-case.xml` (matches URL routing patterns)  
- **Components**: `PascalCase.xsl` (matches React component naming)
- **Build outputs**: Mirror source structure with `.svg` extension

## 🎯 Design Principles

1. **Semantic First**: Screen XML should read like component trees
2. **Data Driven**: All content via data attributes, no hardcoded styling
3. **AI Parseable**: Clear structure for automated React Native conversion
4. **Build Separation**: Source (XML) separate from output (SVG)
5. **Progressive Enhancement**: Start with structure, add styling via transforms

## 🚢 Development Handoff

When designs are complete:

1. **Component Library**: React Native components match XSLT transforms
2. **Screen Routing**: XML filenames become route paths
3. **Data Contracts**: Data attributes define component prop interfaces
4. **Theme System**: XML theme definitions become JavaScript/TypeScript constants

---

*This design system bridges the gap between design and development, ensuring pixel-perfect implementation while maintaining design flexibility.*

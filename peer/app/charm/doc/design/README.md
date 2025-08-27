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
│   ├── onboarding-discovery.md # Discovery-driven onboarding
│   ├── first-friend-tally.md   # First tally relationship setup
│   ├── onboarding-email-tally.md # Email tally invitation response
│   └── ... (other story files)
│
├── specs/                      # Design specifications (human-authored)
│   ├── README.md               # Spec file guidelines and templates
│   ├── home-dashboard.md       # Home screen layout requirements
│   ├── tally-review.md         # Tally setup screen requirements
│   └── ... (one spec per complex screen)
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
Write comprehensive user stories with human-authored sequences and AI-generated scenarios:
- **Human section**: Story overview, step sequence, acceptance criteria
- **AI section**: Detailed scenarios with screen references and thumbnails
- Stories drive screen design requirements

### 2. **Screen Design** (`screens/`)
Create individual screen layouts iteratively:
- Author in semantic XML with data-driven components
- Build generates SVG wireframes for visual review
- **Screen Reuse**: New stories often reuse existing screens
- **Screen Evolution**: Existing screens may need updates for new requirements

### 3. **Iterative Design Process** ⚠️ **CRITICAL**
When stories are processed iteratively, screen designs evolve:

**Screen Modification Impact:**
- ✅ **Screen updated** (e.g., add new component to home-dashboard.xml)
- ❌ **Scenarios outdated** (existing stories referencing that screen)
- 🔄 **Required action**: Re-review ALL existing scenarios that reference the modified screen

**Process for Screen Changes:**
1. **Identify impact**: `grep -r "screen-name.svg" stories/` to find referencing scenarios
2. **Review scenarios**: Check if narrative still matches updated screen
3. **Update scenarios**: Revise AI-generated text to reflect screen changes
4. **Rebuild wireframes**: `./build.sh` to generate updated SVGs
5. **Validate stories**: Ensure screen thumbnails and descriptions align

**Example Workflow:**
```bash
# You modify home-dashboard.xml to add a new "Notifications" section
./build.sh  # Regenerate home-dashboard.svg

# Find all stories that reference this screen
grep -r "home-dashboard.svg" stories/
# Result: onboarding-discovery.md, first-friend-tally.md

# Review and update scenarios in both files to mention new notifications feature
# Scenarios must accurately describe what users see in the updated screen
```

### 4. **Screen Design Guidelines** (`screens/README.md`)
For detailed screen creation guidance, see `screens/README.md`:
- Component usage patterns
- Layout principles  
- Data attribute conventions
- When to create new vs. modify existing screens

### 5. **Component System** (`components/`)
Maintain the reusable design system:
- Update transforms when adding new component types
- Keep theme definitions centralized
- Document component usage patterns in master.xsl comments

### 6. **Cross-Story Validation**
Before marking design phase complete:
- ✅ All scenarios reference current screen versions
- ✅ Screen thumbnails match scenario descriptions
- ✅ No outdated narrative references to removed UI elements
- ✅ New screen features mentioned in relevant scenarios

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

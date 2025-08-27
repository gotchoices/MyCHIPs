# Global Navigation Specifications

*Universal navigation patterns and components for the MyCHIPs mobile app*

## 🧭 Navigation Architecture

### Bottom Tab Bar (Primary Navigation)

**Component**: `<bottom-tab-bar>` with `<tab-item>` elements

**4-Tab Structure**:
1. **Home** (🏠) - Dashboard, balance, recent activity, tally management
2. **Invoice** (📄) - Send/receive payment requests, invoice management  
3. **Scan** (📷) - QR code scanner for payments and tally invitations
4. **Settings** (⚙️) - Account, security, preferences

**Specifications**:
- **Height**: 83px (includes safe area)
- **Background**: White (#FFFFFF)
- **Border**: Top border 1px #E5E5EA
- **Tab Width**: 93.75px each (375px / 4 tabs)
- **Icon Size**: 24px circle background, 12px icon
- **Active State**: Icon background #007AFF, text #007AFF, font-weight 600
- **Inactive State**: Icon background #8E8E93, text #8E8E93, font-weight 500
- **Typography**: SF Pro, 10px tab labels

**Usage in Screens**:
```xml
<bottom-tab-bar x="0" y="729">
    <tab-item data-label="Home" data-icon="🏠" data-active="true" data-icon-color="#007AFF" data-text-color="#007AFF" data-font-weight="600" x="46.875" y="10"/>
    <tab-item data-label="Invoice" data-icon="📄" data-active="false" data-icon-color="#8E8E93" data-text-color="#8E8E93" data-font-weight="500" x="140.625" y="10"/>
    <tab-item data-label="Scan" data-icon="📷" data-active="false" data-icon-color="#8E8E93" data-text-color="#8E8E93" data-font-weight="500" x="234.375" y="10"/>
    <tab-item data-label="Settings" data-icon="⚙️" data-active="false" data-icon-color="#8E8E93" data-text-color="#8E8E93" data-font-weight="500" x="328.125" y="10"/>
</bottom-tab-bar>
```

### Breadcrumb Navigation (Secondary Navigation)

**Component**: `<breadcrumb-bar>` (to be implemented)

**Specifications**:
- **Position**: Below app header, above main content
- **Height**: 44px
- **Background**: Transparent or light gray (#F8F9FA)
- **Typography**: SF Pro, 14px, medium weight
- **Separator**: " > " or chevron icon
- **Max Levels**: 4 levels deep before truncation
- **Truncation**: "... > Parent > Current" for deep paths

**Usage Patterns**:
- **Tab Root**: No breadcrumbs (e.g., Home dashboard)
- **Level 1**: Single breadcrumb (e.g., "Settings > Account")
- **Level 2+**: Full path (e.g., "Tally > Partners > New Partner > Review")

**Usage in Screens**:
```xml
<breadcrumb-bar x="20" y="98">
    <breadcrumb-item data-label="Tally" data-link="tally-home" x="0" y="0"/>
    <breadcrumb-item data-label="Partners" data-link="tally-partners" x="60" y="0"/>
    <breadcrumb-item data-label="Review" data-current="true" x="140" y="0"/>
</breadcrumb-bar>
```

## 📱 Screen Layout Standards

### Universal Screen Structure

**Template**:
```xml
<app-screen width="375" height="812" xmlns="http://mychips.io/ui">
    <!-- Status bar area: 0-44px -->
    <app-header data-title="Screen Title"/> <!-- 44-98px -->
    
    <!-- Optional breadcrumbs: 98-142px -->
    <breadcrumb-bar x="20" y="98">...</breadcrumb-bar>
    
    <!-- Main content area: 142-729px (587px available) -->
    <!-- Content goes here -->
    
    <!-- Bottom tab bar: 729-812px -->
    <bottom-tab-bar x="0" y="729">...</bottom-tab-bar>
</app-screen>
```

### Safe Areas and Spacing

- **Status Bar**: 44px (iPhone safe area)
- **Header**: 54px (title + padding)
- **Breadcrumbs**: 44px (when present)
- **Bottom Tabs**: 83px (tabs + safe area)
- **Content Padding**: 20px horizontal margins
- **Section Spacing**: 24px between major sections

## 🔗 Navigation Transitions

### Tab Navigation
- **Behavior**: Replace entire screen stack
- **Animation**: Cross-fade between tab contents
- **State**: Each tab maintains its own navigation stack

### Modal Presentation
- **Triggers**: Complex forms, detail views, secondary flows
- **Animation**: Slide up from bottom
- **Dismissal**: Swipe down, cancel button, or completion
- **Examples**: Tally creation, QR sharing, payment forms

### Push Navigation
- **Behavior**: Navigate within tab's stack
- **Animation**: Slide from right
- **Back Button**: Always available in header
- **Examples**: Settings subpages, transaction details

## 🎯 Navigation State Management

### Tab State Persistence
- Each tab remembers its navigation stack
- Switching tabs preserves scroll position and form state
- Deep links can target specific tab + screen combination

### Modal State
- Modals are app-level (appear over all tabs)
- Closing modal returns to previous tab state
- Modal navigation is separate from tab navigation

### Back Button Behavior
- **Tab Root**: No back button
- **Tab Stack**: Navigate to previous screen in stack
- **Modal**: Close modal and return to previous tab state

---

*These specifications ensure consistent navigation across all screens and provide clear patterns for AI code generation.*

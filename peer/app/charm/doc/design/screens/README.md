# Screen Definitions

This directory contains the semantic XML source files for individual app screens. These files are transformed into visual SVG wireframes via the build system.

## File Naming Convention

Use kebab-case names that match the intended route structure:
- `auth-login.xml` → `/auth/login` route
- `wallet-overview.xml` → `/wallet/overview` route
- `pay-scan-qr.xml` → `/pay/scan-qr` route

## Navigation Requirements

**BEFORE creating any screen:**
1. Check [`../navigation/sitemap.md`](../navigation/sitemap.md) for proper navigation placement
2. Follow [`../navigation/global-specs.md`](../navigation/global-specs.md) for tab bar requirements
3. Update navigation documentation if adding new sections

## XML Structure

Each screen file uses semantic markup with data attributes:

```xml
<?xml version="1.0" encoding="UTF-8"?>
<?xml-stylesheet type="text/xsl" href="../components/transforms/master.xsl"?>
<app-screen width="375" height="812" xmlns="http://mychips.io/ui">
    
    <app-header data-title="Screen Title"/>
    
    <balance-card 
        data-label="CHIP Balance"
        data-amount="¢1,247.50"
        data-description="Available to spend"/>
    
    <transaction-item
        data-name="Coffee Shop"
        data-amount="-¢8.50"
        data-icon="☕"/>
        
</app-screen>
```

## Building Screens

Generate SVG wireframes from XML source:

```bash
# Build all screens
../build.sh

# Build and view
../build.sh && open ../images/wallet-overview.svg
```

The generated SVG files are placed in `../images/` and referenced by documentation files.

## Design Specifications Integration

Each screen XML file should be accompanied by a corresponding design specification in `../specs/`:

### **Workflow for Screen Creation**

1. **Check for existing spec**: Look in `../specs/[screen-name].md` 
2. **Read design requirements**: Follow layout, interaction, and data specs
3. **Implement in XML**: Create semantic markup that fulfills spec requirements
4. **Reference spec in XML**: Add comment `<!-- Design Requirements: ../specs/[screen-name].md -->`
5. **Build and validate**: Ensure generated SVG matches spec requirements

### **Example Integration**

**Spec file** (`../specs/home-dashboard.md`):
```markdown
## Layout Requirements
- Grand total prominently displayed at top
- Scrollable tally list below total  
- Each tally shows: partner name, CHIP balance, USD equivalent
```

**Screen XML** (`home-dashboard.xml`):
```xml
<!-- Design Requirements: ../specs/home-dashboard.md -->
<app-screen width="375" height="812">
    <balance-summary data-chip-balance="₡1,247.50" data-local-balance="$1,247.50"/>
    <tally-list>
        <tally-item data-partner="Alice" data-balance="₡500.00" data-usd="$500.00"/>
    </tally-list>
</app-screen>
```

### **When to Create Design Specs**

Create a spec file when:
- ✅ **Specific layout requirements** exist beyond user story implications
- ✅ **Complex data presentation** needs detailed formatting rules  
- ✅ **Visual hierarchy** must follow specific product requirements
- ✅ **Interaction behaviors** are more complex than basic navigation

Skip spec file when:
- ❌ **Simple screens** with obvious layouts (basic forms, simple lists)
- ❌ **Standard patterns** that follow common UI conventions
- ❌ **One-off screens** that won't be reused or modified

### **Spec File Benefits**

- **AI reads both** user stories AND design specs when creating screens
- **Human control** over specific layout and interaction requirements
- **Consistency** across multiple stories that use the same screen
- **Clear requirements** that supplement behavioral user stories

## Component Reference

Available semantic components are defined in `../components/transforms/master.xsl`:

### Layout Components
- `<app-header>` - Screen header with title and navigation
- `<app-screen>` - Screen container with dimensions
- `<bottom-tab-bar>` with `<tab-item>` - Bottom navigation

### Content Components  
- `<balance-card>`, `<balance-summary>` - Balance displays
- `<transaction-item>`, `<transaction-list>` - Transaction displays
- `<vendor-item>`, `<vendor-list>` - Marketplace vendor displays
- `<getting-started-item>`, `<getting-started-list>` - Onboarding guidance

### Form Components
- `<input-field>` - Text inputs with labels
- `<button-primary>`, `<button-secondary>` - Action buttons
- `<progress-bar>` - Step indicators
- `<form-section>` - Form grouping

### UI Elements
- `<section-header>` - Section titles
- `<info-card>`, `<info-banner>` - Informational content
- `<context-help>` - Help icons and tooltips
- `<search-bar>` - Search inputs
- `<filter-chip>`, `<filter-chips>` - Filter selections
- `<empty-state>` - Empty/zero state displays

See component transform files for full parameter documentation and examples.

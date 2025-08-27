# Screen Definitions

This directory contains the semantic XML source files for individual app screens. These files are transformed into visual SVG wireframes via the build system.

## File Naming Convention

Use kebab-case names that match the intended route structure:
- `auth-login.xml` → `/auth/login` route
- `wallet-overview.xml` → `/wallet/overview` route
- `pay-scan-qr.xml` → `/pay/scan-qr` route

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

## Component Reference

Available semantic components are defined in `../components/transforms/master.xsl`:

- `<app-header>` - Screen header with title and navigation
- `<balance-card>` - Primary balance display
- `<transaction-item>` - Individual transaction list items
- `<quick-action-card>` - Action buttons
- `<section-header>` - Section titles
- `<action-button-secondary>` - Secondary action buttons
- `<bottom-tab-bar>` with `<tab-item>` - Bottom navigation

See component transform files for full parameter documentation.

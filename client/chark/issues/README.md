# MyCHIPs Mobile App Issues Tracker

This directory contains documentation for various issues, enhancements, upgrades.
Maintain a line in this file, in the appropriate section, for each issues file.
When working on an issue, follow the workflow process in ../CONTEXT.md.

AI Agents:
- Maintain each issue file with enough information to fully restore your context if needed
- Ask the user periodically about issues still marked "In Progress" or Future issues that may now be feasible.

## Important Documentation Files

- [Tally Component Dependencies](tally_deps.md) - Comprehensive analysis of tally-related components, their relationships, and navigation paths. **Keep this file updated whenever modifying tally components**.

## Issue Status Overview

### Completed
- [Deep Linking - Android/iOS](deep-linking.md)
- [iOS Deep Links](ios_deeplinks.md) 
- [React useEffect Dependency Arrays](use_effect.md)
- [Crypto Service Implementation](crypto_service.md) - Centralized crypto service using QuickCrypto
- [QR Code Scanner Compatibility](scanner.md) - Fixed scanner after React Native 0.77 upgrade
- [Tally Display Improvements](tally_display.md) - Enhanced certificate display with interactive elements and image support
- [Tally Validity and Verification](tally_valid.md) - Added cryptographic verification of tallies with visual indicators and repair options

### In Progress
- [Automated Deployment](autodeploy.md) - Fastlane implementation, 90% complete
- [Payment Processing Improvements](payments.md) - Standardizing units, references, UUIDs and timestamps
- [Trading Variables Implementation](trading.md) - Fixing and improving trading variables handling

### Future (Priority Order)
- [Connection Ticket and Backend Connectivity](connect.md) - Improving connection reliability, token handling, and first-time user experience
- [API Communication](api_comm.md) - Optimizing backend communication via Wyseman API
- [Language Text Tags](lang_text.md) - Standardize language text implementation and fill missing tags
- [Toast and Modal UI Improvements](toasting.md) - Standardize feedback mechanisms and user interactions
- [TypeScript Migration](ts_migrate.md) - Migrate codebase to TypeScript
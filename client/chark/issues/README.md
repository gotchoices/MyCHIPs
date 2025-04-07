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
- [Connection Ticket and Backend Connectivity](connect.md) - Fixed critical connection issues including key preservation, confirmation flow, and first-time user experience
- [Automated Deployment](autodeploy.md) - Implemented Fastlane for automated building and deployment to various targets
- [Payment Processing Improvements](payments.md) - Standardized units conversion, UUID generation, and timestamp formats
- [Trading Variables Implementation](trading.md) - Fixed critical issues with trading variables chit generation and processing
- [Language Selection and Auto-Detection](language.md) - Implemented proper default language, locale detection, and fixed Settings UI issues

### In Progress
- [Tally Validity and Verification](tally_valid.md) - Extending cryptographic verification to include chits and hash chain integrity

### Future (Priority Order)
- [Avatar Image Fetching and Display](images.md) - Improving image loading for TallyGraphic and certificate details
- [API Communication](api_comm.md) - Optimizing backend communication via Wyseman API
- [Language Text Tags](lang_text.md) - Standardize language text implementation and fill missing tags
- [Toast and Modal UI Improvements](toasting.md) - Standardize feedback mechanisms and user interactions
- [Trading Variables UI Enhancements](trading.md) - Improve WebView form design and user experience
- [Payment Processing Extensions](payments.md) - Implement consistent memo field handling and additional testing
- [TypeScript Migration](ts_migrate.md) - Migrate codebase to TypeScript
- [Automated Deployment Enhancements](autodeploy.md) - Further CI/CD automation and App Store production releases
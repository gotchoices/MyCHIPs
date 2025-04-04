# MyCHIPs Mobile App Issues Tracker

This directory contains documentation for various issues, enhancements, upgrades.
Maintain a line in this file, in the appropriate section, for each issues file.
When working on an issue, follow the workflow process in ../CONTEXT.md.
AI Agents: ask the user periodically about issues still marked "In Progress" or
Future issues that may now be feasible.

## Issue Status Overview

### Completed
- [Deep Linking - Android/iOS](deep-linking.md)
- [iOS Deep Links](ios_deeplinks.md) 
- [React useEffect Dependency Arrays](use_effect.md)
- [Crypto Service Implementation](crypto_service.md) - Centralized crypto service using QuickCrypto
- [QR Code Scanner Compatibility](scanner.md) - Fixed scanner after React Native 0.77 upgrade

### In Progress
- [Automated Deployment](autodeploy.md) - Fastlane implementation, 90% complete
  - Basic functionality working for all platforms
  - Added automatic external testing group distribution for TestFlight (untested)
  - Remaining: Test App Store production release
- [Payment Processing Improvements](payments.md) - Standardizing units, references, UUIDs and timestamps
  - Added centralized constants and utility functions for unit conversions
  - Improved UUID and timestamp generation for payment chits
  - Standardized reference object handling
  - Remaining: Memo field validation and additional testing
- [Trading Variables Implementation](trading.md) - Fixing and improving trading variables handling
  - Fixed data type conversion for trading parameters
  - Added request status to settings chits
  - Identified improvements needed for web-based trading form
  - Remaining: Units conversion and UI improvements

### Future (Priority Order)
- [API Communication](api_comm.md) - Optimizing backend communication via Wyseman API
- [Language Text Tags](lang_text.md) - Standardize language text implementation and fill missing tags
- [Toast and Modal UI Improvements](toasting.md) - Standardize feedback mechanisms and user interactions
- [TypeScript Migration](ts_migrate.md) - Migrate codebase to TypeScript
# Toast and Modal UI Improvements

*Date: March 22, 2025*

## Overview

This document outlines planned improvements to Toast notifications and Modal dialogs throughout the MyCHIPs mobile application. The focus is on standardizing the UI patterns, improving user feedback, and enhancing the overall user experience.

## Current Issues

1. **Inconsistent Toast and Alert Usage:**
   - Mix of toast notifications and alert dialogs for similar operations
   - No clear pattern for when to use toasts vs. alerts
   - Inconsistent styling and positioning of toast messages

2. **Modal Dialog Inconsistencies:**
   - Some modals use fixed heights while others adapt to content
   - Excessive whitespace in some modals (e.g., PassphraseModal)
   - Inconsistent padding and layout across different modals

3. **Passphrase and Input Handling:**
   - Passphrase confirmation fields don't validate in real-time
   - Some action buttons don't reflect input validity state
   - Unclear feedback for passphrase mismatches

## Improvement Priorities

### 1. Standardize Feedback Mechanisms

- [ ] 1.1 Define clear guidelines for when to use alerts vs. toasts
- [ ] 1.2 Create a centralized toast service for consistent usage patterns
- [ ] 1.3 Ensure all messages use language tags for localization
- [ ] 1.4 Implement standardized toast types (success, error, warning, info)
- [ ] 1.5 Add appropriate feedback for all critical operations

### 2. Modal Dialog Improvements

- [x] 2.1 Refactor CenteredModal to adapt height based on content
- [ ] 2.2 Implement consistent padding and spacing guidelines
- [ ] 2.3 Add standard header/footer patterns for all modals
- [ ] 2.4 Improve keyboard handling for modals with text inputs

### 3. Input Validation Enhancements

- [x] 3.1 Disable action buttons until input requirements are met
- [ ] 3.2 Implement real-time validation for all critical inputs
- [ ] 3.3 Create consistent error messaging patterns for input validation

## Related Work

The recent improvements to the PassphraseModal component in the crypto service implementation (specifically disabling the Export button until passphrases match and making modals adapt to their content) represent the beginning of this effort. These changes have already improved the user experience for key management operations.

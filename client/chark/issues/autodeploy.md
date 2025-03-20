# Automated Build and Deployment Strategy for MyCHIPs Mobile App

## Issue Summary
The MyCHIPs mobile app currently lacks a streamlined automated process for building and deploying to multiple targets (mychips.org, Play Store, App Store/TestFlight), requiring manual intervention and lacking standardized procedures.

## Current Status
- An existing `bin/build` script can build and deploy Android APKs to mychips.org
- iOS build automation is incomplete and untested
- No automated process exists for generating production-ready bundles for store submissions
- No consistent workflow for handling app signing and versioning

## Security Requirements
- App signing keys and keystores must remain on local development machines
- No third-party services should have access to signing credentials
- Build process must support secure, local signing while still enabling automated submission

## Goals
1. **Standardized Build Pipeline**:
   - Create consistent, reproducible builds for both platforms
   - Automate versioning and metadata updates
   - Centralize build configuration

2. **Multi-Target Deployment**:
   - Maintain existing mychips.org deployment capability
   - Add automated submission to Play Store
   - Add automated submission to App Store/TestFlight
   - Clear separation between build and submission steps

3. **Developer Experience**:
   - Simple npm scripts for various build/deploy targets
   - Clear documentation for the build/deployment process
   - Minimal manual steps required

## Proposed Approach: Fastlane Integration with Local Signing

### 1. Implement Fastlane
Fastlane is the industry standard for mobile app deployment automation and addresses our needs:
- Supports both building and submitting apps to both stores
- Works with local signing (keeps keystores on your machine)
- Can automate all aspects: building, signing, versioning, metadata, screenshots, and submissions
- Supports complex workflows via "lanes"

### 2. Build and Submission Architecture
Structure the process with security in mind:
1. **Local Build Phase**: Executed on developer machine with local credentials
   - App signing and packaging
   - Creation of release artifacts
   
2. **Submission Phase**: Could be local or automated via CI
   - Upload to app stores
   - No access to signing keys required for this phase
   - Can use application-specific passwords for Apple and API keys for Google

### 3. Implementation Plan
1. **Phase 1: Fastlane Setup**
   - Install and initialize Fastlane for both platforms
   - Create basic lanes for building signed releases
   - Integrate with existing `bin/build` script

2. **Phase 2: Local Command-Line Workflow**
   - Create npm scripts that invoke Fastlane lanes
   - Add support for increment versioning
   - Document the process thoroughly

3. **Phase 3: App Store Submission**
   - Implement submission lanes for TestFlight
   - Implement submission lanes for Play Store
   - Test end-to-end process

4. **Phase 4: CI/CD Integration (Optional)**
   - If desired, configure GitHub Actions for submissions only
   - Keep signing process local
   - Use encrypted secrets for store credentials only (not signing keys)

## FAQs

### Will I need to upload my keystore to use Fastlane?
No. Fastlane is designed to work with local signing keys. Your Android keystore and iOS certificates remain on your machine.

### Can I automate app store submissions without sharing my signing keys?
Yes. App store submissions can be automated using app-specific passwords (Apple) and API keys (Google Play), which are separate from signing credentials.

### Is Xcode UI necessary for iOS builds and submissions?
No. With Fastlane, the entire process can be automated via command line, including builds, signing, and App Store submission.

### How much of bin/build will remain relevant?
The core functionality can be preserved, but it would be refactored to call Fastlane lanes. The existing SCP deployment to mychips.org can be maintained or incorporated into Fastlane.

## Next Steps
1. Install Fastlane and create initial configuration
2. Create basic build lanes for Android and iOS
3. Update npm scripts in package.json
4. Test and document the process
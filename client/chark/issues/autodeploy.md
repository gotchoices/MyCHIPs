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

### 3. Command Line Interface Approach
After analysis, we recommend using Fastlane directly through npm scripts rather than maintaining a separate bin/build wrapper script:

**Benefits of this approach:**
- Reduces abstraction layers and maintenance overhead
- Provides clear, descriptive commands for different build targets
- Follows industry standards, improving developer onboarding
- Maintains full access to Fastlane's extensive capabilities
- Simplifies documentation and workflow understanding

**Example package.json scripts:**
```json
"scripts": {
  "build:android:apk": "cd android && fastlane build_apk",
  "build:android:bundle": "cd android && fastlane build_app_bundle",
  "deploy:android:mychips": "cd android && fastlane deploy_to_mychips",
  "deploy:android:playstore": "cd android && fastlane deploy_to_playstore",
  "build:ios:archive": "cd ios && fastlane build_archive",
  "deploy:ios:testflight": "cd ios && fastlane beta",
  "deploy:ios:appstore": "cd ios && fastlane release"
}
```

### 4. Implementation Plan
1. **Phase 1: Fastlane Setup**
   - Install and initialize Fastlane for both platforms
   - Create basic lanes for building signed releases
   - Define npm scripts that call Fastlane lanes directly

2. **Phase 2: Feature Implementation**
   - Implement all required build and deployment lanes
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
   
5. **Phase 5: Legacy Script Deprecation**
   - Once the new workflow is proven, deprecate bin/build
   - Provide migration documentation for existing users

## FAQs

### Will I need to upload my keystore to use Fastlane?
No. Fastlane is designed to work with local signing keys. Your Android keystore and iOS certificates remain on your machine.

### Can I automate app store submissions without sharing my signing keys?
Yes. App store submissions can be automated using app-specific passwords (Apple) and API keys (Google Play), which are separate from signing credentials.

### Is Xcode UI necessary for iOS builds and submissions?
No. With Fastlane, the entire process can be automated via command line, including builds, signing, and App Store submission.

### What will happen to bin/build?
We recommend phasing out bin/build entirely in favor of direct Fastlane usage through npm scripts. The existing SCP deployment functionality to mychips.org will be reimplemented as a Fastlane lane. This approach eliminates an unnecessary abstraction layer and leverages Fastlane's full capabilities.

## Implementation Checklist and Progress

### ✅ Completed Tasks
1. ✅ Install Fastlane (`brew install fastlane`)
2. ✅ Create basic Fastlane configuration for Android and iOS
3. ✅ Define essential build and deployment lanes in Fastfiles
4. ✅ Update package.json with npm scripts for Fastlane lanes
5. ✅ Create draft README documentation

### Implementation Status

**Current Version:** 0.2.0 (Updated due to React Native version upgrade)

**Current Implementation:**
- Fastlane has been set up and tested for both Android and iOS
- All build and deployment lanes have been created and verified
- Versioning is managed through npm scripts using react-native-version
- Deployment scripts automatically increment build numbers before deployment
- Android APK and Bundle builds have been tested and verified
- Android Play Store deployment successfully tested
- iOS TestFlight deployment successfully tested
- App Store deployment lane created but not yet tested
- All iOS lanes configured for "MyCHIPs" provisioning profile with Associated Domains capability

**Key Design Decisions:**
- Simplified approach with clear separation of concerns:
  - Versioning handled by npm scripts (using react-native-version)
  - Building and deployment handled by Fastlane
  - No duplication of versioning logic in Fastlane
- Manual semantic versioning in package.json
- Automatic build number increments before deployment
- Direct Fastlane usage through npm scripts rather than maintaining bin/build
- App Store Connect API key authentication using global configuration

**File Structure:**
- `/android/fastlane/`: Android Fastlane configuration
- `/ios/fastlane/`: iOS Fastlane configuration
- Package.json scripts connect these systems together

### 🔲 Remaining Tasks

#### Configuration Customization
- [x] Update Android Appfile with correct package name ✅ (`org.mychips.chark` already set correctly)
- [x] Update iOS Appfile with correct bundle identifier ✅ (`org.mychips.mychips` to match TestFlight)
- [x] Update iOS Appfile with Apple ID and team information ✅ (Using environment variables)
- [x] Review and adjust Fastfiles for project-specific requirements ✅ (Added proper API key handling)
- [x] Add version increment functionality ✅ (Implemented via npm scripts using react-native-version)

#### Signing Setup
- [x] Configure Android signing:
  - [x] Create/locate keystore file and place in appropriate location ✅
  - [x] Update gradle files to reference keystore ✅
  - [x] Test signing configuration with a release build ✅
- [x] Configure iOS signing:
  - [x] Verify certificates and provisioning profiles ✅
  - [x] Ensure provisioning profiles include Associated Domains capability ✅
  - [x] Update Fastlane configuration for proper signing ✅
  - [x] Test signing with a development build ✅

#### Testing and Validation
- [x] Test Android lanes:
  - [x] `build_apk` ✅ (Tested and working)
  - [x] `build_app_bundle` ✅ (Tested and working)
  - [x] `deploy_to_mychips` ✅ (Tested and working with environment variable set)
  - [x] `deploy_to_playstore_testing` ✅ (Tested and working with Google Play API key)
  - [x] `deploy_to_playstore` ✅ (Tested and working, automatic publishing enabled)
- [x] Test iOS lanes:
  - [x] `build_archive` ✅ (Works with proper signing configuration)
  - [x] `test_api_key` ✅ (Added for testing App Store API access)
  - [x] `beta` (TestFlight) ✅ (Successfully uploads to TestFlight)
  - [x] `upload_only` ✅ (Added for uploading existing IPA files)
  - [ ] `release` (App Store) ❓ (Implemented but not yet tested)

#### Documentation
- [x] Finalize README.md updates with Fastlane instructions ✅
- [x] Add comments to Fastfiles explaining each lane ✅
- [x] Document environment variable requirements ✅

#### Environment Variables
- [x] Set up environment variables for deployment:
  - [x] `MYCHIPS_ANDROID_APK_DEPLOY` for Android APK deployment to mychips.org ✅
  - [x] `GOOGLE_PLAY_API_FILE` pointing to Google Play API JSON key file (for Play Store deployment) ✅
  - [x] `APPLE_ID` for Apple Developer account email ✅
  - [x] `APPLE_TEAM_ID` for Apple Developer Portal Team ID ✅
  - [x] `APP_STORE_API_FILE` pointing to App Store API key file (for TestFlight/App Store deployment) ✅

#### Transition Plan
- [x] Add deprecation notice to bin/build ✅
- [x] Create developer transition guidance document ✅ (Added in README.md)
- [x] Run side-by-side tests (old vs new build process) ✅
- [ ] Officially deprecate bin/build after transition period

#### Future Enhancements
- [ ] Test and verify App Store production release
- [ ] Add support for automatically submitting to TestFlight External Testing
- [ ] Add changelog generation or management in deployment process
- [ ] Add safety checks to prevent accidentally uploading debug builds

#### (Optional) CI/CD Integration
- [ ] Research appropriate CI/CD platforms compatible with requirements
- [ ] Create CI configuration for automated builds
- [ ] Set up secure credential storage in CI
- [ ] Configure automated testing in CI pipeline
- [ ] Set up deployment triggers (tags, branches, etc.)

## Implemented Approach

### Versioning Strategy
- Manual semantic versioning in package.json (e.g., 0.2.0)
- Automatic build number increments via react-native-version
- Build numbers are incremented before deployment
- Clear separation between semantic versioning and build numbers

### Build Process
- Fastlane manages all builds
- Separate lanes for different build targets:
  - Android: APK and App Bundle
  - iOS: Archive, TestFlight, and App Store
- Build scripts in package.json provide easy access to Fastlane lanes

### Deployment Process
- Deployment scripts automatically:
  1. Increment build numbers
  2. Build the appropriate artifact
  3. Deploy to the specified target
- Environment variables control deployment destinations

### Environment Variables
- `MYCHIPS_ANDROID_APK_DEPLOY`: SCP destination for Android APKs
- iOS deployment requires Apple Developer credentials

## Documentation Updates Needed
- Update README.md with comprehensive information:
  - Add complete prerequisites section:
    - Node.js, npm/yarn version requirements
    - Xcode and Android Studio installation and configuration
    - Java/Gradle requirements for Android
    - Ruby and Fastlane installation instructions (`brew install fastlane` recommended)
    - Required environment variables and signing setup
  - Expand development environment setup:
    - Testing environment configuration
    - Development workflow best practices
    - Debugging tools and approaches
  - Create detailed build and deployment section:
    - Development builds vs production builds
    - Step-by-step deployment process for each platform and target
    - Clear description of npm script commands for various build/deploy targets
    - Keystore and signing certificate management
  - Add troubleshooting section for common issues:
    - Build failures and their solutions
    - Signing and certificate problems
    - Deployment rejections and resolutions

## Draft README available at: README-fastlane-draft.md
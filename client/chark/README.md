# Chark App

> MyCHIPs React Native Mobile Application

## Prerequisites

### Development Environment
- **Node.js**: v18 or higher
- **npm**: Latest version recommended
- **Ruby**: v2.6 or higher (for Fastlane)
- **Fastlane**: Install via `brew install fastlane` (macOS) or `gem install fastlane` (other platforms)

### iOS Development
- **macOS**: Required for iOS development
- **Xcode**: Latest version recommended
- **CocoaPods**: Install via `gem install cocoapods`
- **Apple Developer Account**: Required for TestFlight and App Store submissions

### Android Development
- **Android Studio**: Latest version
- **Java Development Kit (JDK)**: Version 11
- **Android SDK**: API levels 21-33 recommended
- **Google Play Console Account**: Required for Play Store submissions
- **Android Keystore**: For signing release builds

## Installation

1. Clone the repository:
   ```
   git clone <repository-url>
   cd chark
   ```

2. Install dependencies:
   ```
   npm install
   ```

3. Install iOS dependencies:
   ```
   cd ios && pod install && cd ..
   ```

## Development

### Start Development Server
```
npm start
```

### Build and Run on Android
```
npm run android
```

### Build and Run on iOS
```
npm run ios
```

## Testing

### Run Unit Tests
```
npm test
```

### Run End-to-End Tests (Android)
```
npm run test:android
```

## Build and Deployment

The app uses Fastlane for automated building and deployment. This replaces the older `bin/build` script with a more robust approach. The following npm scripts are available:

### Android Builds

- **Build Release APK** (for direct distribution):
  ```
  npm run build:android:apk
  ```

- **Build App Bundle** (for Play Store):
  ```
  npm run build:android:bundle
  ```

### Android Deployment

- **Deploy APK to mychips.org**:
  ```
  npm run deploy:android:mychips
  ```
  Note: Requires `MYCHIPS_ANDROID_APK_DEPLOY` environment variable to be set with the SCP destination.

- **Deploy to Play Store Open Testing**:
  ```
  npm run deploy:android:testing
  ```
  Note: Requires `GOOGLE_PLAY_API_FILE` environment variable pointing to your Google Play API JSON key file.

- **Deploy to Play Store Production**:
  ```
  npm run deploy:android:release
  ```
  Note: Requires `GOOGLE_PLAY_API_FILE` environment variable pointing to your Google Play API JSON key file.

All Play Store deployments are automatically published to their respective tracks without requiring manual approval in the Google Play Console.

### iOS Builds

- **Build Archive** (for distribution):
  ```
  npm run build:ios:archive
  ```

### iOS Deployment

- **Deploy to TestFlight**:
  ```
  npm run deploy:ios:testflight
  ```
  Note: Requires `APPLE_ID`, `APPLE_TEAM_ID`, and `APP_STORE_API_FILE` environment variables to be set.

- **Upload an existing IPA to TestFlight** (without rebuilding):
  ```
  cd ios && fastlane upload_only
  ```
  This will look for an IPA file at `ios/build/chark.ipa` and upload it to TestFlight.

- **Deploy to App Store**:
  ```
  npm run deploy:ios:appstore
  ```
  Note: Requires `APPLE_ID`, `APPLE_TEAM_ID`, and `APP_STORE_API_FILE` environment variables to be set.

**Important**: When uploading to TestFlight, you'll need to manually enable External Testing through the App Store Connect web interface if desired. The automated deployment only uploads the build but doesn't configure testing groups.

## Signing and Certificates

### Android Signing

1. Create a keystore file if you don't have one:
   ```
   keytool -genkey -v -keystore mychips-key.keystore -alias mychips -keyalg RSA -keysize 2048 -validity 10000
   ```

2. Place the keystore file in `android/app`.

3. Set up environment variables for signing:
   ```
   export APP_STORE_FILE=mychips-key.keystore
   export APP_STORE_PASSWORD=your-keystore-password
   export APP_KEY_PASSWORD=your-key-password
   ```

### Google Play API Setup

To deploy to the Google Play Store, you need to set up API access:

1. Log in to the [Google Play Console](https://play.google.com/console/)

2. Go to **Setup → API access**

3. Click **Create Service Account**, which will take you to the Google Cloud Platform

4. In Google Cloud Platform:
   - Click **Create Service Account**
   - Enter a name (e.g., "fastlane-deploy")
   - Click **Create and Continue**
   - For Role, select **Service Account User**
   - Click **Continue** and then **Done**

5. Create and download the JSON key:
   - Find your service account in the list
   - Click the three dots (more actions) → **Manage keys**
   - Click **Add Key** → **Create new key**
   - Choose JSON format and click **Create**
   - Save this file securely (NOT in your repository)

6. Grant permissions in Play Console:
   - Go back to Play Console → **Setup** → **API access**
   - Find your service account and click **Grant Access**
   - Grant the following permissions:
     - **Release apps to testing tracks**
     - **Manage app testing tracks**
   - Click **Apply**

7. Set the environment variable to point to your key file:
   ```
   export GOOGLE_PLAY_API_FILE=/path/to/your-api-key.json
   ```

8. Test your Google Play API configuration:
   ```
   cd android
   fastlane run validate_play_store_json_key json_key:$GOOGLE_PLAY_API_FILE
   ```
   
   To verify your app's information in the Play Store:
   ```
   fastlane run google_play_track_version_codes package_name:"org.mychips.chark" track:"beta"
   ```
   This will attempt to retrieve version codes from the beta track, confirming both API access and app configuration.

### iOS Signing

1. Set up certificates and provisioning profiles in your Apple Developer account.
   - You need three provisioning profiles:
     - "MyCHIPs Development" - For development builds
     - "MyCHIPs Ad Hoc" - For testing on devices
     - "MyCHIPs App Store" - For TestFlight and App Store distribution

2. Make sure your provisioning profiles include the Associated Domains capability.

3. Update the profile names in the Fastlane configuration if necessary:
   - Open `ios/fastlane/Fastfile`
   - Find the `provisioningProfiles` sections and update the profile names to match yours

### App Store API Setup

To deploy to the App Store and TestFlight, you need to set up API access:

1. Log in to [App Store Connect](https://appstoreconnect.apple.com/)

2. Go to **Users and Access** in the sidebar

3. Click on the **Keys** tab

4. Click the "+" button to create a new key:
   - Name it "MyCHIPs Fastlane Deploy" (or another descriptive name)
   - Select the "App Manager" role (or appropriate role with app upload permissions)
   - Click "Generate"
   - Download the API key file (it will be named `AuthKey_KEYID.p8`)
   - Note the Key ID shown in App Store Connect (e.g., ABC123DE45)
   - Note your Issuer ID (found in the API Keys page under "Issuer ID")

5. Create a JSON file with the following structure:
   ```json
   {
     "key_id": "YOUR_KEY_ID",
     "issuer_id": "YOUR_ISSUER_ID",
     "key": "AuthKey_KEYID.p8",
     "duration": 1200,
     "in_house": false
   }
   ```
   
   Note: The `key` path can be:
   - A relative path (e.g., `"AuthKey_KEYID.p8"`) - relative to the JSON file location
   - An absolute path (e.g., `"/Users/name/.fastlane/AuthKey_KEYID.p8"`)
   
   For simplicity, we recommend placing the .p8 key file in the same directory as your JSON file and using a relative path.

6. Find your Team ID in the Apple Developer Portal:
   - Go to [Apple Developer Portal](https://developer.apple.com/)
   - Click on "Account" in the top right
   - Sign in if prompted
   - Click on "Membership" in the left sidebar
   - Your Team ID is listed under "Team ID" in the Membership Information section

7. Set the environment variables to use the API key:
   ```
   export APPLE_ID="your.email@example.com"
   export APPLE_TEAM_ID="ABCDE12345"
   export APP_STORE_API_FILE="/path/to/your/app_store_api_key.json"
   ```

8. Test your App Store API configuration:
   
   We've added a custom Fastlane lane to easily test your App Store API configuration:
   
   ```
   cd ios
   fastlane test_api_key
   ```
   
   This will:
   1. Validate your App Store Connect API key
   2. Try to access your app in TestFlight
   
   If successful, you'll see success messages for both tests. If there are issues, the lane will provide helpful error messages to guide troubleshooting.
   
   Note: If the app doesn't exist in App Store Connect yet, you'll need to create it before TestFlight deployments will work. The test lane will suggest this if it detects the app doesn't exist.

## Troubleshooting

### Common Build Issues

- **Error: Execution failed for task ':app:processDebugManifest'**
  - Check that the Android SDK is properly configured in your project.

- **iOS build fails with code signing errors**
  - Verify that your certificates and provisioning profiles are correctly set up.
  - Check that the bundle identifier matches your provisioning profile.
  - Ensure the provisioning profile names in Fastfile match your actual profiles (currently configured to use "MyCHIPs").
  - For "No provisioning profile provided" errors, check your export_options configuration.

- **Error during Fastlane execution**
  - Ensure all prerequisites are installed.
  - Check that your authentication credentials are correctly set up.

- **TestFlight external testing not enabled**
  - The automated deployment only uploads to TestFlight but doesn't configure testing groups.
  - After uploading, go to App Store Connect > TestFlight > Your Build > Groups and manually add External Testing groups.
  - You'll need to submit for review before external testers can access the build.

### API Connectivity Issues

- **Google Play API Authentication Errors**
  - Verify the `GOOGLE_PLAY_API_FILE` environment variable points to the correct JSON file
  - Check that the service account has the necessary permissions in the Play Console
  - Ensure the package name in Appfile matches your app's package name in the Play Console
  - Try running `fastlane run validate_play_store_json_key` to verify the key

- **App Store Connect API Authentication Errors**
  - Verify the `APP_STORE_API_FILE` environment variable points to the correct JSON file
  - Check that the API key has not expired (they expire after 180 days by default)
  - Ensure the key, issuer ID, and key ID are correctly specified in the JSON file
  - Confirm the app identifier in Appfile matches your app's bundle ID in App Store Connect
  - Run the test lane to diagnose issues: `cd ios && fastlane test_api_key`
  - Make sure your JSON file has the correct format (see API Setup section above)

- **"App not found" errors**
  - Verify that your app is actually created in the respective app store
  - Check that you're using the correct bundle identifier/package name
  - Ensure your account has access to the app in the respective developer console
  
### Build Rejection Issues

- **App Store Review Rejection**
  - Ensure your app complies with Apple's App Store guidelines.
  - Check privacy settings, usage descriptions, and permissions in your Info.plist.

- **Google Play Store Rejection**
  - Review the Google Play policies for compliance.
  - Ensure your app handles user data according to privacy regulations.

## License

Copyright MyCHIPs.org; See license in root of this package.
# iOS Deep Linking Issues Fixed in MyCHIPs After React Native Migration

## Background

The MyCHIPs mobile app was recently upgraded from React Native 0.70.6 to 0.77.0. After this upgrade, deep linking functionality stopped working properly on iOS while continuing to work on Android.

When the app receives a deep link URL like `https://mychips.org/ticket?host=mychips.net&port=1025&token=a3fb51802cd7ebece95334e1e97c6de2&user=p1003`, the following behavior was observed:

- **Android**: Worked correctly - processed the link and connected to the remote backend
- **iOS**: The app launched/came to foreground, but didn't process the deep link parameters
  - No console.log messages appeared from the `getStateFromPath` function in App.js
  - No connection to backend was established

## Root Cause Analysis: Two-Part Problem

Our investigation revealed a two-part issue:

### Part 1: Missing AppDelegate Methods

During the React Native upgrade from 0.70 to 0.77:

1. The AppDelegate was migrated from Objective-C (.mm) to Swift (.swift)
2. During this migration, the deep link handling methods were lost:
   ```objc
   // These methods were in the old Objective-C AppDelegate but missing in Swift
   - (BOOL)application:(UIApplication *)application openURL:(NSURL *)url options:(NSDictionary<UIApplicationOpenURLOptionsKey,id> *)options
   - (BOOL)application:(UIApplication *)application continueUserActivity:(nonnull NSUserActivity *)userActivity restorationHandler:(nonnull void (^)(NSArray<id<UIUserActivityRestoring>> * _Nullable))restorationHandler
   ```

This is why deep links were being received by iOS (causing the app to launch) but not being passed to React Native's JavaScript bridge.

### Part 2: WebCrypto API Incompatibility

After fixing the AppDelegate methods, deep links were being received but connections still failed to complete. Further investigation revealed:

1. The WebCrypto API (provided by `react-native-webview-crypto`) was no longer functioning properly on iOS with RN 0.77.0
2. The API interface was available (`window.crypto.subtle` existed), but operations timed out and never completed
3. This prevented the authentication flow from completing when opening deep links

## Solution Implementation: Swift Methods + WebCrypto Fix

### Step 1: Add Missing AppDelegate Methods

Created a dynamic bridge to access RCTLinkingManager without a direct import:

1. Added a utility class (ReactNativeUtils.swift) to access Objective-C classes dynamically
2. Added the missing URL handling methods to AppDelegate.swift:
   ```swift
   // Handle opening URLs (custom URL schemes like mychips://)
   override func application(_ app: UIApplication, open url: URL, options: [UIApplication.OpenURLOptionsKey: Any] = [:]) -> Bool {
     // Debug log for troubleshooting
     print("Deep link received in AppDelegate: \(url.absoluteString)")
     
     // Using dynamic bridging to RCTLinkingManager
     return ReactNativeUtils.linkingManager(openURL: url, application: app, options: options)
   }
   
   // Handle Universal Links (https://mychips.org/...)
   override func application(_ application: UIApplication, continue userActivity: NSUserActivity, restorationHandler: @escaping ([UIUserActivityRestoring]?) -> Void) -> Bool {
     if userActivity.activityType == NSUserActivityTypeBrowsingWeb, let url = userActivity.webpageURL {
       // Debug log for troubleshooting
       print("Universal link received in AppDelegate: \(url.absoluteString)")
       
       // Using dynamic bridging to RCTLinkingManager
       return ReactNativeUtils.linkingManager(continueUserActivity: userActivity, restorationHandler: restorationHandler)
     }
     return false
   }
   ```

### Step 2: Fix WebCrypto Implementation

After diagnostic testing confirmed that `react-native-webview-crypto` was incompatible with RN 0.77.0 on iOS, we implemented `react-native-quick-crypto` as the solution:

1. In App.js, replaced react-native-webview-crypto import with react-native-quick-crypto:
   ```javascript
   // Old import
   import PolyfillCrypto from 'react-native-webview-crypto';
   
   // New imports
   import QuickCrypto from 'react-native-quick-crypto';
   import { Buffer } from '@craftzdog/react-native-buffer';
   ```

2. Initialized QuickCrypto with necessary globals at the app level:
   ```javascript
   // Initialize Buffer and QuickCrypto globals
   global.Buffer = Buffer;
   QuickCrypto.install();
   ```

3. Removed the PolyfillCrypto component from the render tree:
   ```javascript
   // Removed:
   <PolyfillCrypto />
   ```

## Testing Method

The deep link functionality was tested using:

```bash
# From project root
./bin/linklaunch "https://mychips.org/ticket?host=mychips.net&port=1025&token=a3fb51802cd7ebece95334e1e97c6de2&user=p1003"
```

## Final Status

The implementation is now complete and successful:

1. ✅ Deep links are properly received by iOS via AppDelegate methods
2. ✅ Deep links are passed to React Native and correctly trigger navigation
3. ✅ WebCrypto operations complete successfully using react-native-quick-crypto
4. ✅ Full connection flow completes with backend
5. ✅ Deep linking works consistently on both iOS and Android

## Key Takeaways

1. When migrating React Native on iOS, special attention must be paid to AppDelegate methods
2. `react-native-webview-crypto` is incompatible with React Native 0.77.0 on iOS
3. `react-native-quick-crypto` provides a superior native implementation of WebCrypto
4. Using the `install()` function from QuickCrypto along with global Buffer support ensures proper WebCrypto functionality

## References

- [React Native Deep Linking Documentation](https://reactnative.dev/docs/linking)
- [Apple Universal Links](https://developer.apple.com/documentation/xcode/allowing-apps-and-websites-to-link-to-your-content)
- [react-native-quick-crypto Documentation](https://github.com/margelo/react-native-quick-crypto)
import UIKit
import React
import React_RCTAppDelegate
import ReactAppDependencyProvider

@objc(AppDelegate)
class AppDelegate: RCTAppDelegate {
  override func application(_ application: UIApplication, didFinishLaunchingWithOptions launchOptions: [UIApplication.LaunchOptionsKey : Any]? = nil) -> Bool {
    self.moduleName = "chark"
    self.dependencyProvider = RCTAppDependencyProvider()

    // You can add your custom initial props in the dictionary below.
    // They will be passed down to the ViewController used by React Native.
    self.initialProps = [:]

    return super.application(application, didFinishLaunchingWithOptions: launchOptions)
  }

  override func sourceURL(for bridge: RCTBridge) -> URL? {
    self.bundleURL()
  }

  override func bundleURL() -> URL? {
#if DEBUG
    RCTBundleURLProvider.sharedSettings().jsBundleURL(forBundleRoot: "index")
#else
    Bundle.main.url(forResource: "main", withExtension: "jsbundle")
#endif
  }
  
  // Handle opening URLs (custom URL schemes like mychips://)
  override func application(_ app: UIApplication, open url: URL, options: [UIApplication.OpenURLOptionsKey: Any] = [:]) -> Bool {
    // Debug log for troubleshooting
    print("Deep link received in AppDelegate: \(url.absoluteString)")
    
    // Using ObjC messaging to call RCTLinkingManager without import
    return ReactNativeUtils.linkingManager(openURL: url, application: app, options: options)
  }
  
  // Handle Universal Links (https://mychips.org/...)
  override func application(_ application: UIApplication, continue userActivity: NSUserActivity, restorationHandler: @escaping ([UIUserActivityRestoring]?) -> Void) -> Bool {
    if userActivity.activityType == NSUserActivityTypeBrowsingWeb, let url = userActivity.webpageURL {
      // Debug log for troubleshooting
      print("Universal link received in AppDelegate: \(url.absoluteString)")
      
      // Using ObjC messaging to call RCTLinkingManager without import
      return ReactNativeUtils.linkingManager(continueUserActivity: userActivity, restorationHandler: restorationHandler)
    }
    return false
  }
}

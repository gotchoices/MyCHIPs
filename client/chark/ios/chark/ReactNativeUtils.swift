import UIKit

@objc class ReactNativeUtils: NSObject {
  
  @objc static func linkingManager(openURL url: URL, application app: UIApplication, options: [UIApplication.OpenURLOptionsKey: Any]) -> Bool {
    let RCTLinkingManagerClass: AnyClass? = NSClassFromString("RCTLinkingManager")
    let selector = NSSelectorFromString("application:openURL:options:")
    
    if let linkingClass = RCTLinkingManagerClass,
       linkingClass.responds(to: selector) {
      
      typealias LinkingFunction = @convention(c) (AnyClass, Selector, UIApplication, URL, [UIApplication.OpenURLOptionsKey: Any]) -> Bool
      let linkingFunction = unsafeBitCast(linkingClass.method(for: selector), to: LinkingFunction.self)
      return linkingFunction(linkingClass, selector, app, url, options)
    }
    
    return false
  }
  
  @objc static func linkingManager(continueUserActivity userActivity: NSUserActivity, restorationHandler: @escaping ([UIUserActivityRestoring]?) -> Void) -> Bool {
    let RCTLinkingManagerClass: AnyClass? = NSClassFromString("RCTLinkingManager")
    let selector = NSSelectorFromString("application:continueUserActivity:restorationHandler:")
    
    if let linkingClass = RCTLinkingManagerClass,
       linkingClass.responds(to: selector) {
      
      typealias LinkingFunction = @convention(c) (AnyClass, Selector, UIApplication, NSUserActivity, @escaping ([UIUserActivityRestoring]?) -> Void) -> Bool
      let linkingFunction = unsafeBitCast(linkingClass.method(for: selector), to: LinkingFunction.self)
      return linkingFunction(linkingClass, selector, UIApplication.shared, userActivity, restorationHandler)
    }
    
    return false
  }
}
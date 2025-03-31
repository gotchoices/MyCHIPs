# MyCHIPs QR Scanner Abstraction

This directory contains a QR code scanning abstraction layer that enables easy switching between different scanner implementations while maintaining a consistent interface.

## Current Implementation

The scanner currently uses **react-native-camera-kit** as the default implementation, which provides a simple and lightweight QR scanning solution.

## Available Implementations

### 1. Camera Kit (Current Default)
- **Library**: `react-native-camera-kit`
- **Status**: Working with React Native 0.77.0
- **Pros**: Simpler API, lightweight, fewer dependencies
- **Cons**: Less powerful, fewer advanced features

### 2. Vision Camera with Barcode Scanner (Alternative)
- **Library**: `react-native-vision-camera` with `@mgcrea/vision-camera-barcode-scanner`
- **Status**: Implemented but untested with React Native 0.77.0
- **Pros**: More powerful, actively maintained, better frame processing
- **Cons**: More complex setup, requires additional dependencies

## How to Switch Implementations

To switch between implementations, edit `index.js` in this directory:

### To use Camera Kit (default):
```javascript
// Use Camera Kit implementation
import CameraKitScanner from './camera-kit-scanner';
export default CameraKitScanner;

// Vision Camera implementation (commented out)
// import VisionCameraScanner from './vision-camera-scanner';
// export default VisionCameraScanner;
```

### To use Vision Camera:
```javascript
// Camera Kit implementation (commented out)
// import CameraKitScanner from './camera-kit-scanner';
// export default CameraKitScanner;

// Use Vision Camera implementation
import VisionCameraScanner from './vision-camera-scanner';
export default VisionCameraScanner;
```

## Android Configuration for Vision Camera

If switching to Vision Camera implementation, you'll need to update Android configuration:

1. In `android/app/build.gradle`, add:
   ```gradle
   dependencies {
     // ML Kit dependency for barcode scanning
     implementation 'com.google.mlkit:barcode-scanning:17.0.3'
     
     // Worklets core for frame processors in vision-camera
     implementation project(':react-native-worklets-core')
   }
   ```

2. In `android/settings.gradle`, add:
   ```gradle
   // Add worklets-core path for vision-camera
   include ':react-native-worklets-core'
   project(':react-native-worklets-core').projectDir = new File(rootProject.projectDir, '../node_modules/react-native-worklets-core/android')
   ```

## Implementation Notes

Both implementations maintain the same core interface with three key props:
1. `style` - Standard React Native style object
2. `isActive` - Boolean to enable/disable QR scanning
3. `onReadCode` - Callback function receiving `event.nativeEvent.codeStringValue`

## Tested Alternatives

During React Native 0.77.0 migration, several scanner implementations were evaluated:

1. **react-native-camera-kit** (current implementation)
   - Basic configuration working with RN 0.77.0

2. **vision-camera-code-scanner**
   - Not compatible with Vision Camera v4.x (requires v2.x)
   - Build errors with MLKit imports

3. **vision-camera-simple-scanner**
   - Compatible with Vision Camera v4.x
   - Worklets integration issues
   - Dependency problems with react-native-worklets-core

4. **@mgcrea/vision-camera-barcode-scanner** (alternative implementation)
   - Actively maintained with recent updates
   - Compatible with Vision Camera v4.x
   - High community adoption
   - Requires additional Android configuration

## Future Development

For future scanner improvements, consider:
1. Testing the Vision Camera implementation more thoroughly
2. Measuring performance of both implementations
3. Adding capability to toggle implementations at runtime
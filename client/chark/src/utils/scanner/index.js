/**
 * Scanner abstraction that allows toggling between camera implementations
 * Focused on the minimal props needed for QR scanning functionality 
 * 
 * To switch implementations, comment/uncomment the appropriate lines below
 * 
 * The abstraction layer contains two implementations:
 * 1. Camera Kit (current): Simpler implementation, lighter weight
 * 2. Vision Camera: More powerful with advanced features
 *    - Note: Vision Camera implementation is included but untested in RN 0.77
 *    - If needed in the future, test thoroughly before deploying
 */

// ===== CAMERA KIT IMPLEMENTATION (current) =====
// Using the default Camera Kit implementation
import CameraKitScanner from './camera-kit-scanner';
export default CameraKitScanner;

// ===== VISION CAMERA IMPLEMENTATION =====
// To use Vision Camera instead, comment out the above lines and uncomment these:
// import VisionCameraScanner from './vision-camera-scanner';
// export default VisionCameraScanner;

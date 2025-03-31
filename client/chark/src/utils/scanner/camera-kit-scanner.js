import React from 'react';
import {Camera, CameraType} from 'react-native-camera-kit';

/**
 * QR scanner implementation using react-native-camera-kit
 * Focusing only on the essential scanning functionality
 * 
 * Props:
 * - style: Standard React Native style object
 * - isActive: Boolean to enable/disable QR scanning
 * - onReadCode: Callback function that must receive an event with structure:
 *               event.nativeEvent.codeStringValue containing the QR code string
 */
const CameraKitScanner = ({
  style,
  isActive,
  onReadCode,
}) => {
  return (
    <Camera
      style={style}
      cameraType={CameraType.Back} // Hard-coded as in Scanner
      flashMode="off"              // Hard-coded as in Scanner
      scanBarcode={isActive}       // Maps to isActive from Scanner
      onReadCode={onReadCode}      // Callback with event.nativeEvent.codeStringValue
      showFrame={true}             // Hard-coded as in Scanner
      laserColor="blue"            // Hard-coded as in Scanner
      frameColor="white"           // Hard-coded as in Scanner
    />
  );
};

export default CameraKitScanner;
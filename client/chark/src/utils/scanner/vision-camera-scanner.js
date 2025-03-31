import React, {useState} from 'react';
import {StyleSheet, Text, View} from 'react-native';
import {Camera, useCameraDevices} from 'react-native-vision-camera';
import {useBarcodeScanner} from '@mgcrea/vision-camera-barcode-scanner';

/**
 * QR scanner implementation using react-native-vision-camera with @mgcrea/vision-camera-barcode-scanner
 * This implementation uses the actively maintained and well-supported barcode scanner library
 * 
 * Props:
 * - style: Standard React Native style object
 * - isActive: Boolean to enable/disable QR scanning
 * - onReadCode: Callback function that must receive an event with structure:
 *               event.nativeEvent.codeStringValue containing the QR code string
 */
const VisionCameraScanner = ({
  style,
  isActive,
  onReadCode,
}) => {
  // Track if we've processed a code to prevent duplicates
  const [lastProcessedCode, setLastProcessedCode] = useState(null);
  const [lastProcessedTime, setLastProcessedTime] = useState(0);
  
  // Get available camera devices
  const devices = useCameraDevices();
  const device = devices.back;
  
  // Set up barcode scanner with QR code format only for better performance
  const { props: cameraProps } = useBarcodeScanner({
    fps: 5,
    barcodeTypes: ['qr'], // Only scan for QR codes
    onBarcodeScanned: (barcodes) => {
      'worklet';
      if (isActive && barcodes.length > 0 && barcodes[0].value) {
        // Process barcodes (handled automatically by the hook)
        processBarcodes(barcodes);
      }
    },
  });

  // Process the detected barcodes (called from the worklet context)
  const processBarcodes = (barcodes) => {
    if (barcodes.length > 0 && barcodes[0].value) {
      const code = barcodes[0].value;
      const now = Date.now();
      
      // Debounce processing to avoid multiple rapid scans (2 second cooldown)
      if (code !== lastProcessedCode || now - lastProcessedTime > 2000) {
        console.log('VisionCamera: QR code detected:', code);
        
        // Normalize the event format to match camera-kit's format
        onReadCode({
          nativeEvent: {
            codeStringValue: code
          }
        });
        
        setLastProcessedCode(code);
        setLastProcessedTime(now);
      }
    }
  };
  
  if (!device) {
    return (
      <View style={[style, styles.container]}>
        <Text style={styles.text}>Loading camera...</Text>
      </View>
    );
  }

  // Enable debugging overlay when not active
  if (!isActive) {
    return (
      <View style={style}>
        <Camera
          style={StyleSheet.absoluteFill}
          device={device}
          isActive={true}
          {...cameraProps}
        />
        <View style={styles.inactiveOverlay}>
          <Text style={styles.inactiveText}>Scanner inactive</Text>
        </View>
      </View>
    );
  }

  return (
    <Camera
      style={style}
      device={device}
      isActive={isActive}
      {...cameraProps}
    />
  );
};

const styles = StyleSheet.create({
  container: {
    justifyContent: 'center',
    alignItems: 'center',
    backgroundColor: '#000',
  },
  text: {
    color: '#fff',
    fontSize: 16,
  },
  inactiveOverlay: {
    position: 'absolute',
    top: 0,
    left: 0,
    right: 0,
    bottom: 0,
    justifyContent: 'center',
    alignItems: 'center',
    backgroundColor: 'rgba(0,0,0,0.5)',
  },
  inactiveText: {
    color: '#fff',
    fontSize: 18,
    fontWeight: 'bold',
  }
});

export default VisionCameraScanner;
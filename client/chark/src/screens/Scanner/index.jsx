import React, { useState, useEffect, useRef } from 'react'
import { StyleSheet, Text } from 'react-native';
import { useCameraDevices, useFrameProcessor, Camera } from 'react-native-vision-camera';
import { useScanBarcodes, BarcodeFormat, scanBarcodes } from 'vision-camera-code-scanner';

import { parse } from '../../utils/query-string';

const Scanner = (props) => {
  const devices = useCameraDevices();
  const device = devices.back;

  const [hasPermission, setHasPermission] = useState(false);
  const [isActive, setIsActive] = useState(true);

  const [frameProcessor, barcodes] = useScanBarcodes([BarcodeFormat.QR_CODE], {
    checkInverted: true,
  });

  const qrCode = barcodes?.[0]?.displayValue;

  useEffect(() => {
    if(qrCode) {
      try {
        setIsActive(false);
        const parsedCode = JSON.parse(qrCode);

        if(parsedCode?.ticket) {
          props.conn.connect({
            ticket: parsedCode?.ticket,
          }, (err, connected) => {
            if(err) {
              console.log('Error connecting: ', err)
            } else if (connected){
              props.navigation.navigate('Home');
            }
          });
        }
      } catch(err) {
        console.log(err.message)
      }
    }
  }, [qrCode, setIsActive])

  useEffect(() => {
    Camera.requestCameraPermission()
      .then(status => {
        setHasPermission(status === 'authorized');
      })
  }, []);

  return (
    device && hasPermission && (
      <Camera
        style={StyleSheet.absoluteFill}
        device={device}
        isActive={isActive}
        frameProcessor={frameProcessor}
        frameProcessorFps={5}
      />
    )
  );
}

const styles = StyleSheet.create({
  barcodeTextURL: {
    fontSize: 20,
    color: 'white',
    fontWeight: 'bold',
  },
});

export default Scanner;

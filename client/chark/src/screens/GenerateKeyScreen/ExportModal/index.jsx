import React, { useRef, useMemo, useEffect } from 'react';
import { View, Alert, PermissionsAndroid, Button, Text, StyleSheet, Platform } from "react-native"
import { encryptJSON, downloadJSONFile, downloadQRCode } from "../../../utils/file-manager";
import ViewShot from 'react-native-view-shot';
import QRCode from 'react-native-qrcode-svg';
import RNFS from 'react-native-fs';

const ExportModal = (props) => {
  const viewShotRef = useRef();
  console.log("From Export", props.passphrase);

  const passphrase = props.passphrase;

  const encryptedData = useMemo(() => {
    return JSON.stringify({
      key: encryptJSON(props.privateKey, passphrase),
    });
  }, [props.privateKey])

  const permissionResult = async () => {
    let granted = false;
    if ((Platform.OS === 'android' && Platform.Version > 29) || Platform.OS === 'ios') {
      granted = true;
    } else {
      granted = await PermissionsAndroid.request(
        PermissionsAndroid.PERMISSIONS.WRITE_EXTERNAL_STORAGE
      );
    }
    return granted;
  }

  const exportToJsonFile = async () => {
    permissionResult().then((granted) => {
      if (granted) {
        downloadJSONFile(encryptedData).then(result => {
          console.log("Saved File to: ", result);
          Alert.alert('Success', 'Saved to downloads', [{ text: "Ok", onPress: props.cancel }]);
        }).catch(ex => {
          console.log("Exception Failed to Save; ", ex);
        })
      } else {
        Alert.alert('Error', `Permission Denied`);
      }
    });
  }

  const exportAsQRCode = async () => {
    permissionResult().then((granted) => {
      if (granted) {
        viewShotRef.current.capture().then(uri => {
          downloadQRCode(uri).then(result => {
            console.log("Saved QR to: ", result);
            Alert.alert('Success', 'QR-Code Saved to downloads', [{ text: "Ok", onPress: props.cancel }]);
          }).catch(ex => {
            console.log("Exception Failed to Save; ", ex);
          })
        });
      } else {
        Alert.alert('Error', `Permission Denied`);
      }
    });
  }

  if (!encryptedData) {
    return <Text>Generating</Text>
  }

  return <View style={styles.container}>
    <View>
      <Text style={styles.jsonText}>{encryptedData}</Text>
      <Button onPress={exportToJsonFile} title="Download as Json" />
      <ViewShot ref={viewShotRef} options={{ format: "png", quality: 1.0 }}>
        <View style={styles.qrView}>
          <QRCode
            value={encryptedData}
            size={200}
          />
        </View>
      </ViewShot>
      <Button onPress={exportAsQRCode} title="Download QR Code" />
      <View style={{ height: 24 }} />
      <Button onPress={props.cancel} title='Cancel' />
    </View>
  </View>
}

const styles = StyleSheet.create({
  container: {
    padding: 12,
  },
  jsonText: {
    padding: 8,
    fontSize: 11,
    backgroundColor: 'black',
    color: 'white',
    marginBottom: 12,
  },
  qrView: {
    alignItems: 'center',
    paddingVertical: 32,
    backgroundColor: 'white',
    marginVertical: 10,
  },
})

export default ExportModal;
import React, { useRef, useEffect, useState } from 'react';
import {
  View,
  Alert,
  PermissionsAndroid,
  Button,
  Text,
  StyleSheet,
  Platform,
  ScrollView,
  ActivityIndicator,
  TouchableWithoutFeedback,
} from "react-native"
import {
  encryptJSON,
  downloadJSONFile,
  downloadQRCode,
  shareQRCode,
  shareJSONFile
} from "../../../../utils/file-manager";
import ViewShot from 'react-native-view-shot';
import QRCode from 'react-native-qrcode-svg';
import { colors } from "../../../../config/constants";
import useMessageText from '../../../../hooks/useMessageText';
import { getLanguageText } from "../../../../utils/language";

const CustomButton = (props) => {
  const onPress =() => {
    props.onPress();
  }

  return (
    <TouchableWithoutFeedback
      onPress={onPress}
    >
      <Text style={{ color: colors.blue, fontFamily: 'inter', fontSize: 14, fontWeight: '500' }}>
        {props.title}
      </Text>
    </TouchableWithoutFeedback>
  )
}

const ExportModal = (props) => {
  const viewShotRef = useRef();

  const passphrase = props.passphrase;
  const [encryptedData, setEncryptedData] = useState(undefined);
  const { messageText } = useMessageText();
  const charkText = messageText?.chark?.msg;

  useEffect(() => {
    // Add defensive checks for the private key
    if (!props.privateKey) {
      Alert.alert("Error", "No private key available to export");
      props.cancel?.();
      return;
    }
    
    // Make sure passphrase is a string
    const safePassphrase = passphrase || "";
    
    encryptJSON(props.privateKey, safePassphrase).then(result => {
      if (result.success) {
        setEncryptedData(result.data);
      } else {
        Alert.alert("Error", result.error || "Failed to encrypt key");
        props.cancel?.();
      }
    }).catch(ex => {
      console.error("Encryption error:", ex);
      Alert.alert("Error", ex.toString());
      props.cancel?.();
    })
  }, [props.privateKey, passphrase])

  const permissionResult = async () => {
    let granted = false;
    if ((Platform.OS === 'android' && Platform.Version > 29)) {
      granted = true;
    } else {
      granted = await PermissionsAndroid.request(
        PermissionsAndroid.PERMISSIONS.WRITE_EXTERNAL_STORAGE
      );
    }
    return granted;
  }

  const downloadAsJson = async () => {
    permissionResult().then((granted) => {
      if (granted) {
        downloadJSONFile(encryptedData).then(result => {
          console.log("Saved File to: ", result);
          Alert.alert('Success', `Saved ${result.filename} to downloads`, [{ text: "Ok" }]);
        }).catch(ex => {
          console.log("Exception Failed to Save; ", ex);
        })
      } else {
        Alert.alert('Error', `Permission Denied`);
      }
    });
  }

  const downloadQrCode = async () => {
    permissionResult().then((granted) => {
      if (granted) {
        viewShotRef.current.capture().then(uri => {
          downloadQRCode(uri).then(result => {
            console.log("Saved QR to: ", result);
            Alert.alert('Success', `QR-Code Saved as ${result.filename} to downloads`, [{ text: "Ok" }]);
          }).catch(ex => {
            console.log("Exception Failed to Save; ", ex);
          })
        });
      } else {
        Alert.alert('Error', `Permission Denied`);
      }
    });
  }

  const onShareFile = () => {
    shareJSONFile(encryptedData).then((result) => {
      Alert.alert('Success', 'Shared file successfully!');
    }).catch(e => {
      console.log("Share Exception ", e);
    });
  }

  const onShareQR = () => {
    viewShotRef.current.capture().then(uri => {
      shareQRCode(uri).then(result => {
        console.log("Shared ", result);
        Alert.alert('Success', 'Shared QR successfully!');
      }).catch(ex => {
        console.log("Exception Failed to Save; ", ex);
      })
    });
  }

  const onKeyAction = () => {
    if(props.onKeyAction) {
      props.onKeyAction();
    }
  }

  // Use the standardized function to get text with fallback
  const shareTitle = getLanguageText(charkText, 'share');
  const qrTitle = getLanguageText(charkText, 'qr');
  const shareQRText = shareTitle + ' ' + qrTitle;

  if (!encryptedData) {
    return <View style={{ flex: 1, alignItems: 'center', justifyContent: 'center' }}>
      <ActivityIndicator style={{ marginBottom: 24 }} />
      <Button onPress={props.cancel} title={getLanguageText(charkText, 'cancel')} />
    </View>
  }

  return <ScrollView style={styles.container}>
    <View>
      <Text style={styles.jsonText}>{encryptedData}</Text>
      <View style={styles.row}>
        <CustomButton
          onPress={onShareFile}
          title={charkText?.share?.title ?? ''}
        />
      </View>

      {Platform.OS === 'android' && (
        <View style={[styles.row, { marginTop: 15 }]}>
          <CustomButton
            onPress={downloadAsJson}
            title={'Download File'}
          />
        </View>
      )}

      <ViewShot ref={viewShotRef} options={{ format: "png", quality: 1.0 }}>
        <View style={styles.qrView}>
          <QRCode
            value={encryptedData}
            size={200}
          />
        </View>
      </ViewShot>

      <View style={[styles.row, { marginBottom: 15 }]}>
        <CustomButton
          onPress={onShareQR}
          title={shareQRText ?? ''}
        />
      </View>

      {Platform.OS === 'android' && (
        <View style={styles.row}>
          <CustomButton
            onPress={downloadQrCode}
            title={'Download QR'}
          />
        </View>
      )}

      {['import', 'generate'].includes(props.action) && (
        <TouchableWithoutFeedback onPress={onKeyAction}>
          <View style={styles.secondaryButton}>
            <Text style={styles.title}>
              {props.action === 'import' && getLanguageText(charkText, 'import')}
              {props.action === 'generate' && getLanguageText(charkText, 'keygen')}
            </Text>
            <Text style={[styles.title, { fontSize: 10 }]}>
              Your active keys will be lost
            </Text>
          </View>
        </TouchableWithoutFeedback>
      )}

      <View style={[styles.row, { marginTop: 15 }]}>
        <CustomButton
          onPress={props.cancel}
          title={getLanguageText(charkText, 'cancel')}
        />
      </View>

    </View>
  </ScrollView>
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
    paddingVertical: 15,
    backgroundColor: 'white',
    marginVertical: 10,
  },
  row: {
    flexDirection: 'row',
    alignItems: 'center',
    justifyContent: 'space-evenly',
  },
  secondaryButton: {
    alignItems: "center",
    justifyContent: "center",
    borderRadius: 20,
    paddingVertical: 8,
    borderColor: colors.blue,
    backgroundColor: colors.blue,
    marginTop: 15,
  },
  title: {
    fontSize: 12,
    fontWeight: "500",
    color: colors.white,
  },
})

export default ExportModal;

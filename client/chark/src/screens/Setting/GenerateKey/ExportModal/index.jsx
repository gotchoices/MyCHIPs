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
import Icon from 'react-native-vector-icons/Ionicons';
import FontAwesome from 'react-native-vector-icons/FontAwesome';
import { colors } from "../../../../config/constants";
import useMessageText from '../../../../hooks/useMessageText';
import { getLanguageText } from "../../../../utils/language";
import { ShareIcon } from '../../../../components/SvgAssets/SvgAssets';
import EyeIcon from '../../../../../assets/svg/eye_icon.svg';

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
  const [signkeyUrl, setSignkeyUrl] = useState(null);
  const [showJsonSection, setShowJsonSection] = useState(false);
  const { messageText } = useMessageText();
  const charkText = messageText?.chark?.msg;

  // Generate the signkey deep link URL from encrypted data
  const generateSignKeyURL = (encryptedData) => {
    if (!encryptedData || !encryptedData.signkey) return null;
    
    const { s, i, d } = encryptedData.signkey;
    
    // Use URLSearchParams-like approach for parameter encoding
    const params = [
      `s=${encodeURIComponent(s)}`,
      `i=${encodeURIComponent(i)}`,
      `d=${encodeURIComponent(d)}`
    ].join('&');
    
    return `https://mychips.org/signkey?${params}`;
  };

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
        const jsonData = JSON.parse(result.data);
        setEncryptedData(jsonData);
        
        // Generate URL for the deep link
        const url = generateSignKeyURL(jsonData);
        setSignkeyUrl(url);
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
        downloadJSONFile(JSON.stringify(encryptedData)).then(result => {
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
    shareJSONFile(JSON.stringify(encryptedData)).then((result) => {
      Alert.alert('Success', 'Shared file successfully!');
    }).catch(e => {
      console.log("Share Exception ", e);
    });
  }

  const onShareQR = () => {
    viewShotRef.current.capture().then(uri => {
      // Pass both the QR image and the link text
      shareQRCode(uri, signkeyUrl).then(result => {
        console.log("Shared ", result);
        Alert.alert('Success', 'Shared QR successfully!');
      }).catch(ex => {
        console.log("Exception Failed to Share: ", ex);
      })
    });
  }

  const copyToClipboard = () => {
    if (!signkeyUrl) return;
    
    try {
      // For React Native 0.63+
      if (typeof Clipboard !== 'undefined' && Clipboard.setString) {
        Clipboard.setString(signkeyUrl);
      } else {
        // Fallback for older versions
        const Clipboard = require('react-native').Clipboard;
        Clipboard.setString(signkeyUrl);
      }
      Alert.alert('Success', 'Link copied to clipboard');
    } catch (error) {
      console.error('Failed to copy to clipboard:', error);
      Alert.alert('Error', 'Failed to copy to clipboard');
    }
  };

  const toggleJsonSection = () => {
    setShowJsonSection(!showJsonSection);
  };

  const onKeyAction = () => {
    if(props.onKeyAction) {
      props.onKeyAction();
    }
  }

  if (!encryptedData) {
    return <View style={{ flex: 1, alignItems: 'center', justifyContent: 'center' }}>
      <ActivityIndicator style={{ marginBottom: 24 }} />
      <Button onPress={props.cancel} title={getLanguageText(charkText, 'cancel')} />
    </View>
  }

  return (
    <ScrollView style={styles.container}>
      <View>
        {/* QR Code Section */}
        <View style={styles.qrContainer}>
          <ViewShot ref={viewShotRef} options={{ format: "png", quality: 1.0 }}>
            <View style={styles.qrView}>
              <QRCode
                value={signkeyUrl || JSON.stringify(encryptedData)}
                size={200}
              />
            </View>
          </ViewShot>
          <TouchableWithoutFeedback onPress={onShareQR}>
            <View style={styles.shareButton}>
              <ShareIcon size={24} color={colors.white} useNativeIcon={true} />
            </View>
          </TouchableWithoutFeedback>
        </View>

        {/* URL Section */}
        <View style={styles.urlContainer}>
          <Text style={styles.urlText} numberOfLines={1} ellipsizeMode="tail">
            {signkeyUrl ? (signkeyUrl.length > 35 ? signkeyUrl.substring(0, 35) + '...' : signkeyUrl) : 'https://mychips.org/signkey?...'}
          </Text>
          <TouchableWithoutFeedback onPress={copyToClipboard}>
            <View style={styles.copyButton}>
              <FontAwesome name="copy" size={18} color={colors.white} />
            </View>
          </TouchableWithoutFeedback>
        </View>

        {/* Toggle JSON File Section */}
        <TouchableWithoutFeedback onPress={toggleJsonSection}>
          <View style={styles.toggleContainer}>
            <Text style={styles.toggleText}>
              {getLanguageText(charkText, 'file') || 'File'}:
            </Text>
            <EyeIcon width={22} height={22} color={colors.blue} />
          </View>
        </TouchableWithoutFeedback>

        {/* JSON File Section - conditionally rendered */}
        {showJsonSection && (
          <View style={styles.jsonSection}>
            <View style={styles.jsonContainer}>
              <ScrollView style={styles.jsonScrollView}>
                <Text 
                  style={styles.jsonText} 
                  selectable={true}
                >
                  {JSON.stringify(encryptedData, null, 2)}
                </Text>
              </ScrollView>
            </View>
            <View style={styles.jsonActions}>
              {Platform.OS === 'ios' && (
                <TouchableWithoutFeedback onPress={onShareFile}>
                  <View style={styles.actionButton}>
                    <ShareIcon size={18} color={colors.white} useNativeIcon={true} />
                  </View>
                </TouchableWithoutFeedback>
              )}
              
              {Platform.OS === 'android' && (
                <TouchableWithoutFeedback onPress={downloadAsJson}>
                  <View style={styles.actionButton}>
                    <FontAwesome name="download" size={18} color={colors.white} />
                  </View>
                </TouchableWithoutFeedback>
              )}
            </View>
          </View>
        )}

        {/* Support for Key Action when applicable */}
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

        {/* Cancel Button */}
        <View style={[styles.row, { marginTop: 15 }]}>
          <CustomButton
            onPress={props.cancel}
            title={getLanguageText(charkText, 'cancel')}
          />
        </View>
      </View>
    </ScrollView>
  );
}

const styles = StyleSheet.create({
  container: {
    padding: 12,
  },
  qrContainer: {
    flexDirection: 'row',
    alignItems: 'center',
    justifyContent: 'center',
    marginBottom: 20,
  },
  qrView: {
    padding: 16,
    backgroundColor: 'white',
    borderRadius: 8,
  },
  shareButton: {
    marginLeft: 12,
    padding: 10,
    backgroundColor: colors.blue,
    borderRadius: 25,
    width: 45,
    height: 45,
    alignItems: 'center',
    justifyContent: 'center',
  },
  urlContainer: {
    flexDirection: 'row',
    alignItems: 'center',
    backgroundColor: colors.gray100 || '#f5f5f5',
    borderRadius: 8,
    paddingHorizontal: 12,
    paddingVertical: 10,
    marginBottom: 16,
  },
  urlText: {
    flex: 1,
    color: colors.black,
    fontSize: 14,
  },
  copyButton: {
    padding: 8,
    backgroundColor: colors.blue,
    borderRadius: 20,
    width: 35,
    height: 35,
    alignItems: 'center',
    justifyContent: 'center',
  },
  toggleContainer: {
    flexDirection: 'row',
    alignItems: 'center',
    marginBottom: 12,
  },
  toggleText: {
    color: colors.black,
    fontSize: 14,
    fontWeight: '500',
    marginRight: 8,
  },
  jsonSection: {
    marginTop: 8,
    marginBottom: 16,
  },
  jsonContainer: {
    borderRadius: 8,
    borderWidth: 1,
    borderColor: colors.gray300,
    backgroundColor: colors.white,
    height: 150,
  },
  jsonScrollView: {
    padding: 12,
  },
  jsonText: {
    color: colors.black,
    fontFamily: 'monospace',
    fontSize: 12,
    lineHeight: 18,
  },
  jsonActions: {
    flexDirection: 'row',
    justifyContent: 'flex-end',
    marginTop: 8,
  },
  actionButton: {
    marginLeft: 16,
    padding: 8,
    backgroundColor: colors.blue,
    borderRadius: 20,
    width: 35,
    height: 35,
    alignItems: 'center',
    justifyContent: 'center',
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
  buttonText: {
    fontSize: 12,
    fontWeight: "500",
    color: colors.white,
  },
  row: {
    flexDirection: 'row',
    alignItems: 'center',
    justifyContent: 'space-evenly',
  },
});

export default ExportModal;
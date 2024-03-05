import React, { useRef, useEffect, useState } from "react";
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
} from "react-native";
import {
  encryptJSON,
  downloadJSONFile,
  downloadQRCode,
  shareQRCode,
  shareJSONFile,
} from "../../../utils/file-manager";
import ViewShot from "react-native-view-shot";
import QRCode from "react-native-qrcode-svg";
import { colors } from "../../../config/constants";

const GenerateImportModal = (props) => {
  const viewShotRef = useRef();

  const passphrase = props.passphrase;
  const [encryptedData, setEncryptedData] = useState(undefined);

  useEffect(() => {
    encryptJSON(props.privateKey, passphrase)
      .then((result) => {
        if (result.success) {
          console.log("Final Data ==> ", result.data);
          setEncryptedData(result.data);
        } else {
          Alert.alert("Error", result.error);
        }
      })
      .catch((ex) => {
        Alert.alert("Error", ex);
      });
  }, [props.privateKey]);

  const permissionResult = async () => {
    let granted = false;
    if (Platform.OS === "android" && Platform.Version > 29) {
      granted = true;
    } else {
      granted = await PermissionsAndroid.request(
        PermissionsAndroid.PERMISSIONS.WRITE_EXTERNAL_STORAGE
      );
    }
    return granted;
  };

  const downloadAsJson = async () => {
    permissionResult().then((granted) => {
      if (granted) {
        downloadJSONFile(encryptedData)
          .then((result) => {
            console.log("Saved File to: ", result);
            Alert.alert("Success", "Saved to downloads", [
              { text: "Ok" },
            ]);
          })
          .catch((ex) => {
            console.log("Exception Failed to Save; ", ex);
          });
      } else {
        Alert.alert("Error", `Permission Denied`);
      }
    });
  };

  const downloadQrCode = async () => {
    permissionResult().then((granted) => {
      if (granted) {
        viewShotRef.current.capture().then((uri) => {
          downloadQRCode(uri)
            .then((result) => {
              console.log("Saved QR to: ", result);
              Alert.alert("Success", "QR-Code Saved to downloads", [
                { text: "Ok" },
              ]);
            })
            .catch((ex) => {
              console.log("Exception Failed to Save; ", ex);
            });
        });
      } else {
        Alert.alert("Error", `Permission Denied`);
      }
    });
  };

  const onShareFile = () => {
    shareJSONFile(encryptedData)
      .then((result) => {
        Alert.alert("Success", "Shared file successfully!");
      })
      .catch((e) => {
        console.log("Share Exception ", e);
      });
  };

  const onShareQR = () => {
    viewShotRef.current.capture().then((uri) => {
      shareQRCode(uri)
        .then((result) => {
          console.log("Shared ", result);
          Alert.alert("Success", "Shared QR successfully!");
        })
        .catch((ex) => {
          console.log("Exception Failed to Save; ", ex);
        });
    });
  };

  if (!encryptedData) {
    return (
      <View
        style={{
          flex: 1,
          alignItems: "center",
          justifyContent: "center",
        }}
      >
        <ActivityIndicator style={{ marginBottom: 24 }} />
        <Button onPress={props.cancel} title="Cancel" />
      </View>
    );
  }

  return (
    <ScrollView style={styles.container}>
      <View>
        <Text style={styles.jsonText}>{encryptedData}</Text>
        <View style={styles.row}>
          <Button onPress={onShareFile} title="Share File" />
          {Platform.OS === "android" ? (
            <Button onPress={downloadAsJson} title="Download File" />
          ) : (
            <></>
          )}
        </View>
        <ViewShot
          ref={viewShotRef}
          options={{ format: "png", quality: 1.0 }}
        >
          <View style={styles.qrView}>
            <QRCode value={encryptedData} size={200} />
          </View>
        </ViewShot>
        <View style={styles.row}>
          <Button onPress={onShareQR} title="Share QR" />
          {Platform.OS === "android" ? (
            <Button onPress={downloadQrCode} title="Download QR" />
          ) : (
            <></>
          )}
        </View>
        <View style={{ height: 24 }} />

        <TouchableWithoutFeedback onPress={props.importKey}>
          <View style={styles.secondaryButton}>
            <Text style={styles.title}>Import Key</Text>
            <Text style={[styles.title, { fontSize: 10 }]}>
              Your active keys will be lost
            </Text>
          </View>
        </TouchableWithoutFeedback>
      </View>
    </ScrollView>
  );
};

const styles = StyleSheet.create({
  container: {
    padding: 12,
  },
  jsonText: {
    padding: 8,
    fontSize: 11,
    backgroundColor: "black",
    color: "white",
    marginBottom: 12,
  },
  qrView: {
    alignItems: "center",
    paddingVertical: 32,
    backgroundColor: "white",
    marginVertical: 10,
  },
  row: {
    flexDirection: "row",
    alignItems: "center",
    justifyContent: "space-evenly",
  },
  secondaryButton: {
    alignItems: "center",
    justifyContent: "center",
    borderRadius: 20,
    paddingVertical: 8,
    borderColor: colors.blue,
    backgroundColor: colors.blue,
  },
  title: {
    fontSize: 12,
    fontWeight: "500",
    color: colors.white,
  },
});

export default GenerateImportModal;

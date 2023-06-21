
import React, { useState } from 'react';
import { Button, StyleSheet, View, Text, ScrollView, Alert, PermissionsAndroid } from 'react-native';
import { Buffer } from 'buffer';
import SInfo from "react-native-sensitive-info";
import downloadFile from './Progress/DownloadManager';
import { saveSecureJSONToFile } from './Progress/FileManager';
import { KeyConfig } from 'wyseman/lib/crypto';
import { writeFileToDownloads } from '../../utils/file-manager';

const GenerateKeyScreen = () => {
  let initialPrivateKey = undefined;
  const subtle = window.crypto.subtle;

  const [publicKey, setPublicKey] = useState(undefined);
  const [privateKey, setPrivateKey] = useState(undefined);

  const generateECDSAKeys = async () => {
    subtle.generateKey(
      KeyConfig,
      true,
      ['sign', 'verify']
    ).then(keyPair => {
      initialPrivateKey = keyPair.privateKey;
      return subtle.exportKey('jwk', keyPair.publicKey)
    }).then((pubKey) => {
      setPublicKey(pubKey);
      return subtle.exportKey('jwk', initialPrivateKey);
    }).then((priKey) => {
      setPrivateKey(priKey)
    }).catch((e) => console.log("Exception ==> ", e));
  };

  const exportKeySecurely = async () => {
    try {
      const value = JSON.stringify(privateKey);
      const savingFirstData = await SInfo.setItem("key1", value, {
        sharedPreferencesName: "mySharedPrefs",
        keychainService: "myKeychain",
        showModal: true,
        touchID: true,
        kSecAccessControl: 'kSecAccessControlBiometryAny',
      });

      console.log('Saved Data => ', savingFirstData);
    } catch (error) {
      console.log(error);
      Alert.alert('Error', `Failed to save JWK file.${error} `);
    }
  }

  const getStoredKey = async () => {
    const gettingFirstData = await SInfo.getItem("key1", {
      sharedPreferencesName: "mySharedPrefs",
      keychainService: "myKeychain",
      showModal: true,
      touchID: true,
      kSecAccessControl: 'kSecAccessControlBiometryAny',
    });

    console.log("Result Data==>", gettingFirstData)
  }

  const writeJsonFile = async () => {
    const granted = await PermissionsAndroid.request(
      PermissionsAndroid.PERMISSIONS.WRITE_EXTERNAL_STORAGE
    );
    if (granted === PermissionsAndroid.RESULTS.GRANTED) {
      writeFileToDownloads(JSON.stringify(privateKey)).then((success) => {
        Alert.alert('Success', `File Saved Successfully`);
      }).catch((err) => {
        Alert.alert('Error', `Failed to save JWK file.${err} `);
      });
    } else {
      Alert.alert('Error', `Permission Denied`);
    }
  }

  return <View style={styles.container}>
    <ScrollView contentContainerStyle={styles.contentContainer}>
      {publicKey && <Text>Public Key: {'\n'} {Buffer.from(JSON.stringify(publicKey)).toString('base64')}</Text>}
      {publicKey && <Text>Public Json Key: {'\n'} {JSON.stringify(publicKey)}</Text>}

      <View style={{ height: 20 }} />

      {privateKey && <Text>Private Key: {'\n'} {Buffer.from(JSON.stringify(privateKey)).toString('base64')}</Text>}
      {privateKey && <Text>Private Json Key: {'\n'} {JSON.stringify(privateKey)}</Text>}

    </ScrollView>
    {/* downloadFileAsJson */}
    <View style={styles.row}>
      {
        publicKey && privateKey ? <Button onPress={writeJsonFile}
          title='Export Key'
        /> : <></>
      }
      <View style={{ width: 16 }} />
      <Button
        onPress={generateECDSAKeys}
        title='Generate Key'
      />
      <View style={{ width: 16 }} />
      <Button
        onPress={getStoredKey}
        title='Get Data'
      />
    </View>
  </View>
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
  },
  contentContainer: {
    padding: 24,
  },
  row: {
    flexDirection: 'row',
    alignItems: 'center',
    justifyContent: 'center',
    backgroundColor: 'white',
    padding: 12,
    margin: 12,
  }
});

export default GenerateKeyScreen

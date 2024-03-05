import React, { useState } from "react"
import { View, StyleSheet, Button, Alert, Text, ScrollView } from "react-native"
import DocumentPicker from 'react-native-document-picker';
import { useSelector } from 'react-redux';

import PassphraseModal from "../Setting/GenerateKey/PassphraseModal";
import CenteredModal from "../../components/CenteredModal";
import { decryptJSON } from "../../utils/file-manager";
import { useEffect } from "react";
import { isKeyStored, storePrivateKey, storePublicKey } from "../../utils/keychain-store";
import { updatePublicKey } from "../../services/profile";
import useSocket from "../../hooks/useSocket";

const ImportKeyScreen = (props) => {
  const params = props.route?.params;
  const [content, setContent] = useState(undefined);
  const [passphraseModal, setPassphraseModal] = useState(false);
  const [privateKey, setPrivateKey] = useState(undefined);
  const [publicKey, setPublicKey] = useState(undefined);
  const { user } = useSelector(state => state.currentUser);
  const { wm } = useSocket();

  const user_ent = user?.curr_eid;

  useEffect(() => {
    if (params) {
      setContent(JSON.stringify(params));
      setPassphraseModal(true);
    }
  }, [params])

  const onImportKey = () => {
    DocumentPicker.pick(
      {
        type: [DocumentPicker.types.allFiles],
        mode: 'open',
      }
    ).then((results) => {
      const result = results[0];
      if (result.uri) {
        readContent(result.uri);
      } else {
        Alert.alert('Error', 'Failed to select file');
      }
    }).catch((err) => {
      Alert.alert("Error", `${err.error}`);
    });
  };

  const readContent = async (fileUri) => {
    try {
      const response = await fetch(fileUri);
      const jsonData = await response.json();
      setContent(JSON.stringify(jsonData));
      setPassphraseModal(true);
    } catch (err) {
      Alert.alert('Error', `Failed to select file ${err}`);
    }
  };

  const decryptKey = (passphrase) => {
    setPassphraseModal(false);
    decryptJSON(content, passphrase)
      .then((data) => {
        setPrivateKey(data);
        const publicKey = JSON.parse(data);
        delete publicKey.d;
        publicKey.key_ops = ['verify'];
        setPublicKey(JSON.stringify(publicKey));
        console.log("EXPORTED_PUBLIC_KEY ==> ", publicKey);
      })
      .catch(e => {
        console.log("Decrept Ex ", e);
        Alert.alert("Error", e.toString());
      });
  }

  const onUseKey = async () => {
    const { keyStored, message } = await isKeyStored();
    if (keyStored) {
      Alert.alert(
        "Generate Keys",
        message,
        [
          { text: "Cancel" },
          { text: "Proceed", onPress: storeKeys }
        ]
      );
    } else {
      storeKeys();
    }
  }

  const storeKeys = () => {
    updatePublicKey(wm, {
      public_key: JSON.parse(publicKey),
      where: {
        user_ent
      }
    }).then(_ => {
      return Promise.all(
        [
          storePublicKey(publicKey),
          storePrivateKey(privateKey)
        ]
      )
    }).then(() => {
      Alert.alert("Success", "Keys  saved successfully");
    }).catch(ex => {
      Alert.alert("Error", ex.message);
      console.log("EXCEPTION ==> ", ex);
    });
  }

  return <>
    <ScrollView
      style={styles.container}
      contentContainerStyle={styles.contentContainer}
    >
      {privateKey && <Text style={{ marginBottom: 12 }}>PRIVATE KEY: {privateKey}</Text>}
      {publicKey && <Text style={{ marginVertical: 12 }}>PUBLIC KEY: {publicKey}</Text>}
      <View style={{ height: 24 }} />
      <Button
        onPress={onImportKey}
        title="Import Key"
      />
      <View style={{ height: 24 }} />
      {publicKey && <Button
        onPress={onUseKey}
        title="Use Imported Key"
      />}
    </ScrollView>
    <CenteredModal
      isVisible={passphraseModal}
      onClose={() => { setPassphraseModal(false) }}
    >
      <PassphraseModal
        onPassphraseConfirmed={decryptKey}
        cancel={() => {
          setPassphraseModal(false);
        }}
      />
    </CenteredModal>
  </>
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
  },
  contentContainer: {
    paddingHorizontal: 12,
    paddingVertical: 24,
    margin: 16,
    backgroundColor: 'white',
  }
})

export default ImportKeyScreen;

import React, { useState } from "react"
import { View, StyleSheet, Button, Alert, Text } from "react-native"
import DocumentPicker from 'react-native-document-picker';
import PassphraseModal from "../GenerateKeyScreen/PassphraseModal";
import CenteredModal from "../../components/CenteredModal";
import { decryptJSON } from "../../utils/file-manager";

const ImportKeyScreen = () => {
  const [content, setContent] = useState(undefined);
  const [passphraseModal, setPassphraseModal] = useState(false);
  const [privateKey, setPrivateKey] = useState(undefined);

  const onImportKey = async () => {
    const options = {
      type: [DocumentPicker.types.allFiles],
      mode: 'open',
    };
    DocumentPicker.pick(options).then((results) => {
      const result = results[0];
      if (result.uri && result.type === 'application/json') {
        readContent(result.uri);
      } else {
        Alert('Error', 'Failed to select file');
      }
    }).catch((err) => {
      Alert('Error', `Failed to select file ${err}`);
    });
  };

  const readContent = async (fileUri) => {
    try {
      const response = await fetch(fileUri);
      const jsonData = await response.json();
      setContent(jsonData.key);
      setPassphraseModal(true);
    } catch (err) {
      console.log('Error reading file:', err);
      Alert('Error', `Failed to select file ${err}`);
    }
  };

  const decreptData = (passphrase) => {
    setPassphraseModal(false);
    decryptJSON(content, passphrase)
      .then((data) => {
        console.log("Decrepted Data ", data);
        setPrivateKey(data);

      })
      .catch(e => {
        console.log("Decrept Ex ", e);
        Alert.alert("Error", "Failed to decrept");
      });
  }

  return <>
    <View style={styles.container}>
      {privateKey && <Text style={{ marginVertical: 12 }}>{privateKey}</Text>}
      <Button
        onPress={onImportKey}
        title="Import Key" />
    </View>
    <CenteredModal
      isVisible={passphraseModal}
      onClose={() => { setPassphraseModal(false) }}
    >
      <PassphraseModal
        onPassphraseConfirmed={decreptData}
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
    padding: 24,
  },
})

export default ImportKeyScreen;
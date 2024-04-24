import React, { useEffect, useState } from 'react';
import { TextEncoder, TextDecoder } from 'web-encoding';
import { Button, StyleSheet, View, Text, ScrollView, Alert } from 'react-native';
import { useSelector } from 'react-redux';

import { isKeyStored, storePrivateKey, storePublicKey } from '../../../../utils/keychain-store';

import CenteredModal from '../../../../components/CenteredModal';
import ExportModal from '../ExportModal';
import PassphraseModal from '../PassphraseModal';
import { updatePublicKey } from '../../../../services/profile';
import useSocket from '../../../../hooks/useSocket';
import useMessageText from '../../../../hooks/useMessageText';

const PostGenerate = (props) => {
  const { user } = useSelector(state => state.currentUser);
  const { wm } = useSocket();

  const { messageText } = useMessageText();
  const charkText = messageText?.chark?.msg;

  const user_ent = user?.curr_eid;
  const publicKey = props.publicKey;
  const privateKey = props.privateKey;

  const [passphrase, setPassphrase] = useState(undefined);
  const [showModal, setShowModal] = useState(false);
  const [passphraseModal, setPassphraseModal] = useState(false);

  useEffect(() => {
    if (passphrase) {
      setShowModal(true);
    }
  }, [passphrase])


  const checkIfKeyStored = async () => {
    const { keyStored, message } = await isKeyStored();
    if (keyStored) {
      Alert.alert(
        "Generate Keys",
        message,
        [
          { text: charkText?.cancel?.title ?? ''},
          { text: charkText?.proceed?.title ?? '', onPress: storeKeys }
        ]
      );
    } else {
      storeKeys();
    }
  }

  const storeKeys = () => {
    updatePublicKey(wm, {
      public_key: publicKey,
      where: {
        user_ent
      }
    }).then(result => {
      return Promise.all(
        [
          storePublicKey(JSON.stringify(publicKey)),
          storePrivateKey(JSON.stringify(privateKey))
        ]
      )
    }).then(() => {
      Alert.alert("Success", "Keys  saved successfully");
    }).catch(ex => {
      Alert.alert("Error", ex.message);
      console.log("EXCEPTION ==> ", ex);
    });
  }

  const onExportKeys = () => {
    setPassphraseModal(true);
  }

  return (
    <>
      <View style={styles.container}>
        <ScrollView contentContainerStyle={styles.contentContainer}>
          {publicKey && <Text>Public Json Key: {'\n'} {JSON.stringify(publicKey)}</Text>}
          <View style={{ height: 20 }} />
          {privateKey && <Text>Private Json Key: {'\n'} {JSON.stringify(privateKey)}</Text>}
        </ScrollView>

        <View>
          <View style={styles.row}>
            {
              !!publicKey && !!privateKey && (
                <Button onPress={onExportKeys} title={charkText?.export?.title ?? ''} />
              )
            }
            <View style={{ width: 16 }} />
            <Button
              onPress={checkIfKeyStored}
              title='Use Generated Keys'
            />
          </View>

          <View style={[styles.row, { marginTop: 1, marginBottom: 12 }]}>
            <Button
              onPress={props.onClose}
              title={charkText?.cancel?.title ?? ''}
            />
          </View>
        </View>
      </View>

      <CenteredModal
        isVisible={showModal}
        onClose={() => setShowModal(false)}
      >
        <ExportModal
          privateKey={JSON.stringify(privateKey)}
          cancel={() => {
            setPassphrase(undefined);
            setShowModal(false);
          }}
          passphrase={passphrase}
        />
      </CenteredModal>

      <CenteredModal
        isVisible={passphraseModal}
        onClose={() => { setPassphraseModal(false) }}
      >
        <PassphraseModal
          onPassphraseConfirmed={(passphrase) => {
            setPassphrase(passphrase);
            setPassphraseModal(false);
          }}
          cancel={() => {
            setPassphraseModal(false);
          }}
        />
      </CenteredModal>
    </>
  )
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
    marginHorizontal: 12,
  }
});

export default PostGenerate;

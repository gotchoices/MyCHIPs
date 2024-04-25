import React, { useEffect, useState } from 'react';
import { TextEncoder, TextDecoder } from 'web-encoding';
import { Button, StyleSheet, View, Text, ScrollView, Alert } from 'react-native';
import { useSelector } from 'react-redux';

import { isKeyStored, retrieveKey, storePrivateKey, storePublicKey } from '../../../../utils/keychain-store';

import CenteredModal from '../../../../components/CenteredModal';
import ExportModal from '../ExportModal';
import PassphraseModal from '../PassphraseModal';
import { createSignature, verifySignature } from '../../../../utils/message-signature';
import { keyServices } from '../../../../config/constants';
import { updatePublicKey } from '../../../../services/profile';
import useSocket from '../../../../hooks/useSocket';
import { promptBiometrics } from '../../../../services/biometrics';

const PostGenerate = (props) => {
  const encoder = new TextEncoder();
  const decoder = new TextDecoder();
  const message = "My message is verified";
  const data = encoder.encode(message);

  const { user } = useSelector(state => state.currentUser);
  const { wm } = useSocket();

  const user_ent = user?.curr_eid;
  const publicKey = props.publicKey;
  const privateKey = props.privateKey;

  const [passphrase, setPassphrase] = useState(undefined);
  const [showModal, setShowModal] = useState(false);
  const [passphraseModal, setPassphraseModal] = useState(false);
  const [signature, setSignature] = useState()

  useEffect(() => {
    if (passphrase) {
      setShowModal(true);
    }
  }, [passphrase])


  const signMessage = async () => {
    await promptBiometrics("Use biometrics to create a signature")
    
    createSignature(message).then(signature => {
      console.log("Signature ==> ", signature);
      setSignature(signature);
      Alert.alert("Success", 'Message signed success');
    }).catch(e => {
      console.log("Exception ==> ", e)
      Alert.alert("Error", e.toString());
    });
  }

  const verifyMessage = async () => {
    const creadentials = await retrieveKey(keyServices.publicKey);
    console.log("PUBLIC_KEY ==> ", creadentials.password);

    await promptBiometrics("Use biometrics to verify your signature")

    verifySignature(
      signature,
      message,
      creadentials.password
    ).then(verified => {
      if (verified) {
        Alert.alert("Success", `Message verified: ${verified} \nDecoded Message: ${decoder.decode(data)}`);
      } else {
        Alert.alert("Error", `Failed to verify message`);
      }
    }).catch(ex => {
      console.log("Why Failed==>", ex);
      Alert.alert("Error", ex.message);
    });
  }

  const checkIfKeyStored = async () => {
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
                <Button onPress={onExportKeys} title='Export Key' />
              )
            }
            <View style={{ width: 16 }} />
            <Button
              onPress={checkIfKeyStored}
              title='Use Generated Keys'
            />
          </View>

          {/* <View style={[styles.row, { marginTop: 1, marginBottom: 12 }]}>
            <Button
              onPress={signMessage}
              title='Sign Message'
            />
            <View style={{ width: 16 }} />
            <Button
              onPress={verifyMessage}
              title='Verify Message'
            />
          </View> */}

          <View style={[styles.row, { marginTop: 1, marginBottom: 12 }]}>
            <Button
              onPress={props.onClose}
              title='Cancel'
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

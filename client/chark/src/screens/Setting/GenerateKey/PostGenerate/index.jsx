import React, { useEffect, useState } from 'react';
import { TextEncoder, TextDecoder } from 'web-encoding';
import { Button, StyleSheet, View, Text, ScrollView, Alert } from 'react-native';
import { KeyConfig, SignConfig } from 'wyseman/lib/crypto';

import { retrieveKey, storePrivateKey, storePublicKey } from '../../../../utils/keychain-store';

import CenteredModal from '../../../../components/CenteredModal';
import ExportModal from '../ExportModal';
import PassphraseModal from '../PassphraseModal';
import { exportFile } from '../../../../utils/file-manager';
import { createSignature, verifySignature } from '../../../../utils/message-signature';
import { keyServices } from '../../../../config/constants';
import { updatePublicKey } from '../../../../services/profile';
import useSocket from '../../../../hooks/useSocket';
import useCurrentUser from '../../../../hooks/useCurrentUser';

const PostGenerate = (props) => {
  const encoder = new TextEncoder();
  const decoder = new TextDecoder();
  const message = "My message is verified";
  const data = encoder.encode(message);

  const { user } = useCurrentUser();
  const { wm } = useSocket();

  const user_ent = user?.curr_eid;

  const subtle = window.crypto.subtle;
  const publicKey = props.publicKey;
  const privateKey = props.privateKey;

  const [passphrase, setPassphrase] = useState(undefined);
  const [showModal, setShowModal] = useState(false);
  const [passphraseModal, setPassphraseModal] = useState(false);

  // For testing only
  const [signature, setSignature] = useState()

  useEffect(() => {
    if (passphrase) {
      setShowModal(true);
    }
  }, [passphrase])


  const signMessage = async () => {
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

  const storeKeys = () => {
    updatePublicKey(wm, {
      public_key: publicKey,
      where: {
        user_ent
      }
    }).then(result => {
      console.log("PUBLIC KEY UP ==> ", result);
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

  const getMyKey = async () => {
    try {
      const credentials = await retrieveKey(keyServices.privateKey)
      Alert.alert("Success", `Key Fetched : ${credentials.password}`);
    } catch (err) {
      Alert.alert("Error", err.message);
    }
  }

  const onExportKeys = () => {
    setPassphraseModal(true);
    /*  console.log("Private Key ", privateKey);
    exportFile(privateKey).then(file => {
      console.log("Key Here", file);
    }) */
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
              onPress={storeKeys}
              title='Save Keys'
            />
          </View>

          {/* <View style={[styles.row, { marginTop: 1 }]}>
            <Button
              onPress={storeKeys}
              title='Save Keys'
            />
            <View style={{ width: 16 }} />
            <Button
              onPress={getMyKey}
              title='Get Pvt Key'
            />
          </View> */}

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
          cancel={() => setShowModal(false)}
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

import React, { useEffect, useState } from 'react';
import { TextEncoder, TextDecoder } from 'web-encoding';
import { Button, StyleSheet, View, Text, ScrollView, Alert } from 'react-native';
import { KeyConfig, SignConfig } from 'wyseman/lib/crypto';

import { retrieveKey, storeKey } from '../../../../utils/keychain-store';

import CenteredModal from '../../../../components/CenteredModal';
import ExportModal from '../ExportModal';
import PassphraseModal from '../PassphraseModal';

const PostGenerate = (props) => {
  const encoder = new TextEncoder();
  const decoder = new TextDecoder();
  const data = encoder.encode("Hello world!");

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
    try {
      const credentials = await retrieveKey('private_key')

      const pvtKey = JSON.parse(credentials.password);
      // const pvtKey = privateKey;
      const priv = await subtle.importKey('jwk', pvtKey, KeyConfig, true, ['sign']);

      const sign = await subtle.sign(SignConfig, priv, data);

      setSignature(sign);
      Alert.alert("Success", "Message signed successfully");
    } catch (err) {
      console.log("Error ", err)
    }
  }

  const verifyMessage = async () => {
    try {
      const pub = await subtle.importKey('jwk', publicKey, KeyConfig, true, ['verify'])
      const verified = await subtle.verify(
        SignConfig,
        pub,
        signature,
        data,
      );

      if (verified) {
        Alert.alert("Success", `Message verified: ${verified} \nDecoded Message: ${decoder.decode(data)}`);
      } else {
        Alert.alert("Error", `Failed to verify message`);
      }

    } catch (err) {
      Alert.alert("Error", ex.message);
    }
  }

  const storeMykey = async () => {
    try {
      await storeKey(JSON.stringify(privateKey));
      Alert.alert("Success", "Private key saved successfully");
    } catch (err) {
      Alert.alert("Error", err.message);
    }
  }

  const getMyKey = async () => {
    try {
      const credentials = await retrieveKey('private_key')
      Alert.alert("Success", `Key Fetched : ${credentials.password}`);
    } catch (err) {
      Alert.alert("Error", err.message);
    }
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
          </View>

          <View style={[styles.row, { marginTop: 1 }]}>
            <Button
              onPress={storeMykey}
              title='Store Key'
            />
            <View style={{ width: 16 }} />
            <Button
              onPress={getMyKey}
              title='Get Key'
            />
          </View>

          <View style={[styles.row, { marginTop: 1, marginBottom: 12 }]}>
            <Button
              onPress={signMessage}
              title='Sign Message'
            />
            <View style={{ width: 16 }} />
            <Button
              onPress={verifyMessage}
              title='Verify Message'
            />
          </View>

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

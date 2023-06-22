
import React, { useState } from 'react';
import { Button, StyleSheet, View, Text, ScrollView } from 'react-native';
import { KeyConfig } from 'wyseman/lib/crypto';
import { easyKey, retrieveKey, storeKey } from './keychain-store';
import CenteredModal from '../../components/CenteredModal';
import ExportModal from './ExportModal';

const GenerateKeyScreen = () => {
  let initialPrivateKey = undefined;
  const subtle = window.crypto.subtle;

  const [publicKey, setPublicKey] = useState(undefined);
  const [privateKey, setPrivateKey] = useState(undefined);
  const [showModal, setShowModal] = useState(false);

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

  const storeMykey = () => {
    storeKey(JSON.stringify(privateKey)).then(result => {
      console.log('Key Saved ', result);
    }).catch(err => {
      console.log("Key Save Error ", err);
    });
  }

  const getMyKey = () => {
    retrieveKey('private_key').then(credentials => {
      console.log("Credentials ", credentials);
    }).catch(err => {
      console.log("Error ", err)
    });
  }

  return <>
    <View style={styles.container}>
      <ScrollView contentContainerStyle={styles.contentContainer}>
        {publicKey && <Text>Public Json Key: {'\n'} {JSON.stringify(publicKey)}</Text>}

        <View style={{ height: 20 }} />

        {privateKey && <Text>Private Json Key: {'\n'} {JSON.stringify(privateKey)}</Text>}

      </ScrollView>

      <View>
        <View style={styles.row}>
          {
            publicKey && privateKey ? <Button onPress={() => setShowModal(true)}
              title='Export Key'
            /> : <></>
          }
          <View style={{ width: 16 }} />
          <Button
            onPress={generateECDSAKeys}
            title='Generate Key'
          />
          <View style={{ width: 16 }} />

        </View>
        <View style={[styles.row, { marginTop: 1, marginBottom: 12 }]}>
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
      </View>

    </View>

    <CenteredModal
      isVisible={showModal}
      onClose={() => setShowModal(false)}
    >
      <ExportModal
        privateKey={JSON.stringify(privateKey)}
        cancel={() => setShowModal(false)}
      />
    </CenteredModal >
  </>
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

export default GenerateKeyScreen


import React, { useEffect, useState } from 'react';
import { Button, StyleSheet, View, Text, ScrollView } from 'react-native';
import { KeyConfig, SignConfig } from 'wyseman/lib/crypto';
import { retrieveKey, storeKey } from './keychain-store';
import CenteredModal from '../../components/CenteredModal';
import ExportModal from './ExportModal';
import PassphraseModal from './PassphraseModal';
import { TextEncoder } from 'web-encoding';
const MyConfig = {
  name: 'ECDSA',
  hash: { name: 'SHA-256' },
};

const GenerateKeyScreen = () => {
  const encoder = new TextEncoder();
  const data = encoder.encode("Hello world");

  let signature = undefined;
  const subtle = window.crypto.subtle;
  let currentKeyPair = { publicKey: undefined, privateKey: undefined };

  let myPriKey = undefined;

  const [publicKey, setPublicKey] = useState(undefined);
  const [privateKey, setPrivateKey] = useState(undefined);
  const [passphrase, setPassphrase] = useState(undefined);
  const [showModal, setShowModal] = useState(false);
  const [passphraseModal, setPassphraseModal] = useState(false);

  useEffect(() => {
    if (passphrase) {
      setShowModal(true);
    }
  }, [passphrase])

  const generateECDSAKeys = async () => {
    subtle.generateKey(
      KeyConfig,
      true,
      ['sign', 'verify']
    ).then(keyPair => {
      myPriKey = keyPair.privateKey;
      currentKeyPair = { publicKey: keyPair.publicKey, privateKey: keyPair.privateKey };
      return subtle.exportKey('jwk', keyPair.publicKey);
    }).then((pubKey) => {
      setPublicKey(pubKey);
      return subtle.exportKey('jwk', currentKeyPair.privateKey);
    }).then((priKey) => {
      setPrivateKey(priKey)
    }).catch((e) => console.log("Exception ==> ", e));
  };

  const encryptMessage = async () => {
    try {
      const enco = new TextEncoder();
      const dataone = encoder.encode('message');

      console.log("Data ", dataone);
      const sig = await subtle.sign(
        SignConfig,
        myPriKey,
        dataone,
      );
      console.log("Signature ", sig);
    }
    catch (ex) {
      console.log("Exception, ", ex);
    }
  }

  const decryptMessage = () => {
    subtle.verify(
      MyConfig,
      currentKeyPair.publicKey,
      signature,
      data,
    ).then(verified => {
      console.log("Verified ==> ", verified);
    }).catch(e => console.log('Exeption ==> ', e));
  }


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

  const onExportKeys = () => {
    setPassphraseModal(true);
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
            publicKey && privateKey ? <Button onPress={onExportKeys} title='Export Key' />
              : <></>
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

        <View style={[styles.row, { marginTop: 1, marginBottom: 12 }]}>
          <Button
            onPress={encryptMessage}
            title='Encrypt Message'
          />
          <View style={{ width: 16 }} />
          <Button
            onPress={decryptMessage}
            title='Decrypt Message'
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

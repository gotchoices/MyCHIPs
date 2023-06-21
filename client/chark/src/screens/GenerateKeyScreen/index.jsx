
import React, { useEffect, useState } from 'react';
import { Button, StyleSheet, View, NativeModules, Text, ScrollView } from 'react-native';
import { Buffer } from 'buffer';
import { stringify } from 'querystring';

const config = {
  name: 'ECDSA',
  namedCurve: 'P-521'
};

const GenerateKeyScreen = () => {
  let initialPrivateKey = undefined;
  const [publicKey, setPublicKey] = useState(undefined);
  const [privateKey, setPrivateKey] = useState(undefined);


  useEffect(() => {
    console.log("Public Key ==> ", publicKey);
    console.log("Private Key ==> ", privateKey);

  }, [publicKey, privateKey]);

  const subtle = window.crypto.subtle;

  const generateECDSAKeys = async () => {
    subtle.generateKey(
      config,
      true,
      ['sign', 'verify']
    )
      .then(keyPair => {
        initialPrivateKey = keyPair.privateKey;
        return subtle.exportKey('jwk', keyPair.publicKey)
      })
      .then((pubKey) => {
        setPublicKey(pubKey);
        return subtle.exportKey('jwk', initialPrivateKey);
      }).then((priKey) => {
        setPrivateKey(priKey)
      })
      .catch((e) => console.log("Exception ==> ", e));

  };

  return <ScrollView style={styles.container} contentContainerStyle={styles.contentContainer}>
    <Button
      onPress={generateECDSAKeys}
      title='Generate Key'
    />

    {publicKey && <Text>Public Key: {'\n'} {Buffer.from(JSON.stringify(publicKey)).toString('base64')}</Text>}
    {publicKey && <Text>Public Json Key: {'\n'} {JSON.stringify(publicKey)}</Text>}

    <View style={{ height: 20 }} />

    {privateKey && <Text>Private Key: {'\n'} {Buffer.from(JSON.stringify(privateKey)).toString('base64')}</Text>}
    {privateKey && <Text>Private Json Key: {'\n'} {JSON.stringify(privateKey)}</Text>}

  </ScrollView>
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
  },
  contentContainer: {
    padding: 24,
  }
});

export default GenerateKeyScreen

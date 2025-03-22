import React, { useState } from 'react';
import { StyleSheet, Text, TouchableOpacity, View } from 'react-native';

import CenteredModal from '../../../components/CenteredModal';
import PostGenerate from './PostGenerate';
import Spinner from '../../../components/Spinner';

import { KeyConfig } from '../../../config/constants';
import { generateKeyPair, exportKey } from '../../../services/crypto';

const GenerateKey = (props) => {

  const [generating, setGenerating] = useState(false);
  const [publicKey, setPublicKey] = useState(undefined);
  const [privateKey, setPrivateKey] = useState(undefined);
  const [showPostGenerateModal, setShowPostGenerateModal] = useState(false);

  const generateECDSAKeys = async () => {
    try {
      setGenerating(true);
      // Use the crypto service to generate and export keys
      const keyPair = await generateKeyPair(KeyConfig, ['sign', 'verify']);

      const currentKeyPair = { publicKey: keyPair.publicKey, privateKey: keyPair.privateKey };
      const pubKey = await exportKey('jwk', keyPair.publicKey);
      setPublicKey(pubKey);

      const priKey = await exportKey('jwk', currentKeyPair.privateKey);
      setPrivateKey(priKey)
      setShowPostGenerateModal(true);
    } catch (err) {
      console.log('Error generating key', err);
    } finally {
      setGenerating(false);
    }
  };

  return (
    <>
      <TouchableOpacity
        style={{ width: "100%", flexDirection: 'row' }}
        onPress={generateECDSAKeys}
      >
        <Text style={[props.menuStyle, { marginRight: 5 }]}>Generate Keys</Text>
        {generating && <Spinner size="small" />}
      </TouchableOpacity>

      <CenteredModal
        isVisible={showPostGenerateModal}
        onClose={() => setShowPostGenerateModal(false)}
      >
        <PostGenerate
          onClose={() => setShowPostGenerateModal(false)}
          publicKey={publicKey}
          privateKey={privateKey}
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
  },
});

export default GenerateKey

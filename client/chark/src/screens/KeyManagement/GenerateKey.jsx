import React, { useState } from 'react';
import { useSelector, useDispatch } from 'react-redux';
import { View, Text, StyleSheet } from 'react-native';

import Button from '../../components/Button';
import SigningKeyWarning from '../../components/SigningKeyWarning';
import BottomSheetModal from '../../components/BottomSheetModal';

import useSocket from '../../hooks/useSocket';
import { colors, KeyConfig } from '../../config/constants';
import { updatePublicKey } from '../../services/profile';
import { storePrivateKey, storePublicKey } from '../../utils/keychain-store';
import { setPrivateKey, setPublicKey } from '../../redux/profileSlice';

const GenerateKey = () => {
  const subtle = window.crypto.subtle;
  const dispatch = useDispatch();

  const { wm } = useSocket();
  const { user } = useSelector(state => state.currentUser);

  const [showGenerateWarning, setShowGenerateWarning] = useState(false);
  const [generating, setGenerating] = useState(false);

  const user_ent = user?.curr_eid;

  const onGenerateClick = () => {
    setShowGenerateWarning(true);
  }

  const onGenerateCancel = () => {
    setShowGenerateWarning(false);
  }

  const onAccept = async () => {
    try {
      setGenerating(true);
      const keyPair = await subtle.generateKey(KeyConfig, true, ['sign', 'verify'])

      const publicKey = await subtle.exportKey('jwk', keyPair.publicKey);
      const privateKey = await subtle.exportKey('jwk', keyPair.privateKey);

      await updatePublicKey(wm, {
        public_key: publicKey,
        where: {
          user_ent
        }
      })

      const strPublicKey = JSON.stringify(publicKey);
      const strPrivateKey = JSON.stringify(privateKey);
      await Promise.all(
        [
          storePublicKey(strPublicKey),
          storePrivateKey(strPrivateKey)
        ]
      )

      dispatch(setPublicKey(strPublicKey))
      dispatch(setPrivateKey(strPrivateKey))
      onGenerateCancel();
    } catch (err) {
      console.log('Error generating key', err);
    } finally {
      setGenerating(false);
    }
  }

  return (
    <>
      <View style={{ marginTop: 30 }}>
        <Text style={styles.generate}>Generate</Text>
        <Text style={styles.description}>
          Generating a new key can be a destructive action. Remember to save your current active key by exporting it to a safe place.
        </Text>

        <Button
          style={{ marginTop: 16, width: '50%', height: 30 }}
          title="Generate"
          onPress={onGenerateClick}
        />

      </View>

      <BottomSheetModal
        isVisible={showGenerateWarning}
        onClose={null}
      >
        <SigningKeyWarning
          loading={generating}
          onAccept={onAccept}
          onCancel={onGenerateCancel}
          title="Generating a new key is a destructive action"
          description={`When you open a tally it is signed with a key and needs that key to operate.\n\nIt’s recommended to export and save your keys before you generate new ones.`}
        />
      </BottomSheetModal>
    </>
  )
}

const styles = StyleSheet.create({
  generate: {
    color: colors.black,
    fontSize: 15,
    fontFamily: 'inter',
    fontWeight: '500',
  },
  description: {
    color: colors.gray300,
    fontWeight: '500',
    fontFamily: 'inter',
    fontSize: 12,
    lineHeight: 13,
  }
});

export default GenerateKey;

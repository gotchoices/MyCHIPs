import React, {useState} from 'react';
import {useSelector, useDispatch} from 'react-redux';
import {View, Text, StyleSheet, Alert} from 'react-native';

import Button from '../../components/Button';
import SigningKeyWarning from '../../components/SigningKeyWarning';
import BottomSheetModal from '../../components/BottomSheetModal';

import useSocket from '../../hooks/useSocket';
import {colors, KeyConfig} from '../../config/constants';
import {updatePublicKey} from '../../services/profile';
import {storePrivateKey, storePublicKey} from '../../utils/keychain-store';
import {setPrivateKey, setPublicKey} from '../../redux/profileSlice';
import CenteredModal from '../../components/CenteredModal';
import ExportModal from '../Setting/GenerateKey/ExportModal';
import SuccessContent from '../../components/SuccessContent';
import PassphraseModal from '../Setting/GenerateKey/PassphraseModal';

import {promptBiometrics} from '../../services/biometrics';
import {generateKeyPair, exportKey} from '../../services/crypto';

const GenerateKey = (props) => {
  const dispatch = useDispatch();

  const {wm} = useSocket();
  const {user} = useSelector(state => state.currentUser);

  const [showGenerateWarning, setShowGenerateWarning] = useState(false);
  const [generating, setGenerating] = useState(false);

  const [showSuccess, setShowSuccess] = useState(false);
  const [passphrase, setPassphrase] = useState(undefined);
  const [showKeyModal, setShowKeyModal] = useState(false);
  const [passphraseModal, setPassphraseModal] = useState(false);

  const {privateKey} = useSelector(state => state.profile);

  const user_ent = user?.curr_eid;

  const onGenerateClick = () => {
    if (privateKey) {
      setShowGenerateWarning(true);
    } else {
      onAccept();
    }
  };

  const onGenerateCancel = () => {
    setShowGenerateWarning(false);
  };

  const onAccept = async () => {
    try {
      await promptBiometrics('Confirm biometrics to generate key');

      generateKey();
    } catch (err) {
      alert(err);
    }
  };

  const generateKey = async () => {
    try {
      setGenerating(true);
      
      // Use the crypto service to generate and export keys
      const keyPair = await generateKeyPair(KeyConfig, ['sign', 'verify']);
      const publicKey = await exportKey('jwk', keyPair.publicKey);
      const privateKey = await exportKey('jwk', keyPair.privateKey);

      await updatePublicKey(wm, {
        public_key: publicKey,
        where: {
          user_ent,
        },
      });

      const strPublicKey = JSON.stringify(publicKey);
      const strPrivateKey = JSON.stringify(privateKey);
      await Promise.all([
        storePublicKey(strPublicKey),
        storePrivateKey(strPrivateKey),
      ]);

      dispatch(setPublicKey(strPublicKey));
      dispatch(setPrivateKey(strPrivateKey));
      setShowSuccess(true);
    } catch (err) {
      Alert.alert('Error', err.message);
    } finally {
      setGenerating(false);
    }
  };

  return (
    <>
      <View style={{marginTop: 30}}>
        <Text style={styles.generate}>{props?.text?.keygen?.title ?? 'chark:keygen:title'}</Text>
        <Text style={styles.description}>
          {props?.text?.keygen?.help ?? 'chark:keygen:help'}
        </Text>

        <Button
          style={{marginTop: 16, width: '50%', height: 30}}
          title={props?.text?.keygen?.title ?? 'chark:keygen:title'}
          onPress={onGenerateClick}
        />
      </View>

      <BottomSheetModal
        isVisible={showGenerateWarning}
        onClose={onGenerateCancel}>
        <SigningKeyWarning
          loading={false}
          onAccept={() => {
            setShowGenerateWarning(false);
            if (privateKey) {
              setPassphraseModal(true);
            } else {
              onAccept();
            }
          }}
          onCancel={onGenerateCancel}
          title={props?.text?.keywarn?.title ?? 'chark:keywarn:title'}
          description={props?.text?.keywarn?.help ?? 'chark:keywarn:help'}
        />
      </BottomSheetModal>

      <CenteredModal
        isVisible={showKeyModal}
        onClose={() => setShowKeyModal(false)}>
        <ExportModal
          action="generate"
          privateKey={privateKey}
          cancel={() => {
            setPassphrase(undefined);
            setShowKeyModal(false);
          }}
          onKeyAction={() => {
            setShowKeyModal(false);
            onAccept();
          }}
          passphrase={passphrase}
        />
      </CenteredModal>

      <CenteredModal
        isVisible={passphraseModal}
        onClose={() => {
          setPassphraseModal(false);
        }}>
        <PassphraseModal
          action="generate"
          title={props?.text?.keypass?.title ?? 'chark:keypass:title'}
          subTitle={props?.text?.keypass?.help ?? 'chark:keypass:help'}
          onPassphraseConfirmed={passphrase => {
            setPassphrase(passphrase);
            setPassphraseModal(false);
            setShowKeyModal(true);
          }}
          cancel={() => {
            setPassphraseModal(false);
          }}
          onWithoutExport={() => {
            setPassphraseModal(false);
            onAccept();
          }}
        />
      </CenteredModal>

      <BottomSheetModal
        isVisible={showSuccess}
        onClose={() => setShowSuccess(false)}>
        <SuccessContent
          message={props?.text?.success?.title ?? "chark:success:title"}
          onDone={() => setShowSuccess(false)}
          onDismiss={() => setShowSuccess(false)}
        />
      </BottomSheetModal>
    </>
  );
};

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
  },
});

export default GenerateKey;
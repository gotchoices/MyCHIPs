import React, {useState} from 'react';
import {useSelector, useDispatch} from 'react-redux';
import {View, Text, StyleSheet} from 'react-native';

import Button from '../../components/Button';
import CenteredModal from '../../components/CenteredModal';
import ExportModal from '../Setting/GenerateKey/ExportModal';
import PassphraseModal from '../Setting/GenerateKey/PassphraseModal';

import {colors} from '../../config/constants';
import {keyServices} from '../../config/constants';
import {retrieveKey} from '../../utils/keychain-store';
import {setPrivateKey} from '../../redux/profileSlice';

import ReactNativeBiometrics from 'react-native-biometrics';

const Export = props => {
  const dispatch = useDispatch();
  const [passphrase, setPassphrase] = useState(undefined);
  const [showKeyModal, setShowKeyModal] = useState(false);
  const [passphraseModal, setPassphraseModal] = useState(false);

  const {privateKey} = useSelector(state => state.profile);

  const getKey = async () => {
    const rnBiometrics = new ReactNativeBiometrics();

    rnBiometrics.isSensorAvailable().then(result => {
      const {available, error} = result;
      if (available) {
        return rnBiometrics
          .simplePrompt({
            promptMessage: props.text?.keybio?.title ?? 'Biometric Validation',
          })
          .then(() => {
            return exportKey();
          })
          .catch(err => {
            alert(props.text?.biofail?.help ?? 'Unable to access your private key because your biometric validation failed.');
          });
      }

      return exportKey();
    });
  };

  const exportKey = async () => {
    try {
      let key = privateKey;
      if (!key) {
        priKey = await retrieveKey(keyServices.privateKey);
        key = priKey.password;
        dispatch(setPrivateKey(key));
      }
      if (!key) {
        Alert.alert(props.text?.export?.title ?? '', props.text?.nokey?.help);
      }

      setPassphraseModal(true);
    } catch (err) {}
  };

  return (
    <>
      <View style={{marginTop: 30}}>
        <Text style={styles.exportText}>{props.text?.export?.title ?? ''}</Text>
        <Text style={styles.exportDescription}>
          {props?.text?.keywarn?.help ?? ''}
        </Text>

        <Button
          style={styles.exportBtn}
          title={props.text?.export?.title ?? ''}
          onPress={getKey}
        />
      </View>

      <CenteredModal
        isVisible={showKeyModal}
        onClose={() => setShowKeyModal(false)}>
        <ExportModal
          privateKey={privateKey}
          cancel={() => {
            setPassphrase(undefined);
            setShowKeyModal(false);
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
          action="export"
          onPassphraseConfirmed={passphrase => {
            setPassphrase(passphrase);
            setPassphraseModal(false);
            setShowKeyModal(true);
          }}
          cancel={() => {
            setPassphraseModal(false);
          }}
        />
      </CenteredModal>
    </>
  );
};

const styles = StyleSheet.create({
  exportText: {
    color: colors.black,
    fontSize: 15,
    fontFamily: 'inter',
    fontWeight: '500',
  },
  exportDescription: {
    color: colors.gray300,
    fontWeight: '500',
    fontFamily: 'inter',
    fontSize: 12,
    lineHeight: 13,
  },
  exportBtn: {
    marginTop: 16,
    width: '50%',
    height: 30,
  },
});

export default Export;

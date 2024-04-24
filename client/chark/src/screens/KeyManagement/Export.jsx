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

import {promptBiometrics} from '../../services/biometrics';

const Export = props => {
  const dispatch = useDispatch();
  const [passphrase, setPassphrase] = useState(undefined);
  const [showKeyModal, setShowKeyModal] = useState(false);
  const [passphraseModal, setPassphraseModal] = useState(false);

  const {privateKey} = useSelector(state => state.profile);

  const getKey = async() => {
    try {
     await promptBiometrics('Confirm biometrics to generate key')

      exportKey();
    } catch (err) {
      alert(err);
    }
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
        Alert.alert('Export Key', 'Seems like you have no saved keys.');
      }

      setPassphraseModal(true);
    } catch (err) {
      alert(err);
    }
  };

  return (
    <>
      <View style={{marginTop: 30}}>
        <Text style={styles.exportText}>{props.exportText}</Text>
        <Text style={styles.exportDescription}>
          Generating a new key can be a destructive action. Remember to save
          your current active key by exporting it to a safe place.
        </Text>

        <Button
          style={styles.exportBtn}
          title={props.exportText}
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

import React, {useEffect, useState} from 'react';
import {View, Text, StyleSheet, Alert} from 'react-native';

import Button from '../../components/Button';
import SigningKeyWarning from '../../components/SigningKeyWarning';
import BottomSheetModal from '../../components/BottomSheetModal';

import {colors} from '../../config/constants';
import {useDispatch, useSelector} from 'react-redux';
import CenteredModal from '../../components/CenteredModal';
import PassphraseModal from '../Setting/GenerateKey/PassphraseModal';
import ExportModal from '../Setting/GenerateKey/ExportModal';

import DocumentPicker from 'react-native-document-picker';
import {decryptJSON} from '../../utils/file-manager';
import {
  isKeyStored,
  storePrivateKey,
  storePublicKey,
} from '../../utils/keychain-store';

import {updatePublicKey} from '../../services/profile';
import useSocket from '../../hooks/useSocket';

import {promptBiometrics} from '../../services/biometrics';

const ImportKey = props => {
  const [showImportWarning, setShowImportWarning] = useState(false);
  const [showKeyModal, setShowKeyModal] = useState(false);
  const [passphraseModal, setPassphraseModal] = useState(false);
  const [passphrase, setPassphrase] = useState(undefined);
  const {privateKey} = useSelector(state => state.profile);
  const [prevPassphraseModal, setPrevPassphraseModal] = useState(false);
  const [content, setContent] = useState(undefined);

  const [newPrivateKey, setNewPrivateKey] = useState(undefined);
  const [newPublicKey, setNewPublicKey] = useState(undefined);

  const {user} = useSelector(state => state.currentUser);
  const {wm} = useSocket();

  const user_ent = user?.curr_eid;

  useEffect(() => {
    if (newPublicKey) {
      onUseKey();
    }
  }, [newPublicKey]);

  const onImportError = () => {
    setPassphraseModal(false);

    Alert.alert('Error', 'Failed to select file');
  };

  const onImportKey = async () => {
    try {
      await promptBiometrics('Confirm biometrics to generate key');
      importKeys();
    } catch (err) {
      alert(err);
    }
  };

  const importKeys = async () => {
    try {
      DocumentPicker.pick({
        type: [DocumentPicker.types.allFiles],
        mode: 'open',
        requestLongTermAccess: false,
      })
        .then(results => {
          const result = results[0];
          if (result.uri) {
            setPassphraseModal(false);
            readContent(result.uri);
          } else {
            onImportError();
          }
        })
        .catch(err => {
          if (DocumentPicker.isCancel(err)) {
            onImportError();
          }
        });
    } catch (err) {
      if (DocumentPicker.isCancel(err)) {
        onImportError();
      }
    }
  };

  const readContent = async fileUri => {
    try {
      const response = await fetch(fileUri);
      const jsonData = await response.json();
      setShowKeyModal(false);
      setContent(JSON.stringify(jsonData));
      setPrevPassphraseModal(true);
    } catch (err) {
      Alert.alert('Error', `Failed to select file ${err}`);
    }
  };

  const decryptKey = passphrase => {
    setPrevPassphraseModal(false);
    decryptJSON(content, passphrase)
      .then(data => {
        setNewPrivateKey(data);
        const publicKey = JSON.parse(data);
        delete publicKey.d;
        publicKey.key_ops = ['verify'];
        setNewPublicKey(JSON.stringify(publicKey));
        console.log('EXPORTED_PUBLIC_KEY ==> ', publicKey);
      })
      .catch(e => {
        console.log('Decrept Ex ', e);
        Alert.alert('Error', e.toString());
      });
  };

  const onUseKey = async () => {
    const {keyStored, message} = await isKeyStored();
    if (keyStored) {
      Alert.alert('Generate Keys', message, [
        {text: 'Cancel'},
        {text: 'Proceed', onPress: storeKeys},
      ]);
    } else {
      storeKeys();
    }
  };

  const storeKeys = () => {
    updatePublicKey(wm, {
      public_key: JSON.parse(newPublicKey),
      where: {
        user_ent,
      },
    })
      .then(a => {
        console.log(a);
        return Promise.all([
          storePublicKey(newPublicKey),
          storePrivateKey(newPrivateKey),
        ]);
      })
      .then(() => {
        Alert.alert('Success', 'Keys  saved successfully');
      })
      .catch(ex => {
        Alert.alert('Error', ex.message);
        console.log('EXCEPTION ==> ', ex);
      });
  };

  const onImportClick = () => {
    if (privateKey) {
      setShowImportWarning(true);
    } else {
      onAccept();
    }
  };

  const onImportCancel = () => {
    setShowImportWarning(false);
  };

  const onAccept = () => {
    setShowImportWarning(false);
    // props.navigation.navigate('ImportKey')
    setPassphraseModal(true);
  };

  return (
    <>
      <View style={{marginTop: 30}}>
        <Text style={styles.importText}>{props?.text?.import?.title ?? 'chark:import:title'}</Text>
        <Text style={styles.importDescription}>
          {props?.text?.import?.help ?? 'chark:import:help'}
        </Text>

        <Button
          style={styles.importBtn}
          title={props?.text?.import?.title ?? 'chark:import:title'}
          onPress={onImportClick}
        />
      </View>

      <BottomSheetModal isVisible={showImportWarning} onClose={onImportCancel}>
        <SigningKeyWarning
          loading={false}
          title={props?.text?.keywarn?.title ?? 'chark:keywarn:title'}
          description={props?.text?.keywarn?.help ?? 'chark:keywarn:help'}
          onAccept={onAccept}
          onCancel={onImportCancel}
        />
      </BottomSheetModal>

      <CenteredModal
        isVisible={passphraseModal}
        onClose={() => {
          setPassphraseModal(false);
        }}>
        <PassphraseModal
          action="import"
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
            onImportKey();
          }}
        />
      </CenteredModal>

      <CenteredModal
        isVisible={showKeyModal}
        onClose={() => setShowKeyModal(false)}>
        <ExportModal
          action="import"
          privateKey={privateKey}
          cancel={() => {
            setPassphrase(undefined);
            setPassphraseModal(false);
            setShowKeyModal(false);
          }}
          onKeyAction={() => onImportKey()}
          passphrase={passphrase}
        />
      </CenteredModal>

      <CenteredModal
        isVisible={prevPassphraseModal}
        onClose={() => setPrevPassphraseModal(false)}>
        <PassphraseModal
          action="import_without"
          onPassphraseConfirmed={decryptKey}
          cancel={() => {
            setPrevPassphraseModal(false);
          }}
          buttonTitle={props?.text?.import?.button ?? 'chark:import:button'}
        />
      </CenteredModal>
    </>
  );
};

const styles = StyleSheet.create({
  importText: {
    color: colors.black,
    fontSize: 15,
    fontFamily: 'inter',
    fontWeight: '500',
  },
  importDescription: {
    color: colors.gray300,
    fontWeight: '500',
    fontFamily: 'inter',
    fontSize: 12,
    lineHeight: 13,
  },
  importBtn: {
    marginTop: 16,
    width: '50%',
    height: 30,
  },
});

export default ImportKey;
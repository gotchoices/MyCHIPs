import React, { useEffect, useState } from 'react';
import { Alert, StyleSheet, Text, TouchableOpacity, View } from 'react-native';
import { retrieveKey } from '../../../../utils/keychain-store';
import { keyServices } from '../../../../config/constants';
import Spinner from '../../../../components/Spinner';
import CenteredModal from '../../../../components/CenteredModal';
import ExportModal from '../ExportModal';
import PassphraseModal from '../PassphraseModal';

const ExportKey = (props) => {
  const [generating, setGenerating] = useState(false);
  const [privateKey, setPrivateKey] = useState(undefined);
  const [passphrase, setPassphrase] = useState(undefined);
  const [showModal, setShowModal] = useState(false);
  const [passphraseModal, setPassphraseModal] = useState(false);

  useEffect(() => {
    if (passphrase) {
      setShowModal(true);
    }
  }, [passphrase])

  const findKeys = async () => {
    try {
      setGenerating(true);
      const priKey = await retrieveKey(keyServices.privateKey);
      if (priKey) {
        setPrivateKey(priKey.password);
        setPassphraseModal(true);
      } else {
        Alert.alert("Export Key", "Seems like you have no saved keys.")
      }
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
        onPress={findKeys}
      >
        <Text style={[props.menuStyle, { marginRight: 5 }]}>Export Saved Key</Text>
        {generating && <Spinner size="small" />}
      </TouchableOpacity>


      <CenteredModal
        isVisible={showModal}
        onClose={() => setShowModal(false)}
      >
        <ExportModal
          privateKey={privateKey}
          cancel={() => {
            setPassphrase(undefined);
            setShowModal(false)
          }}
          passphrase={passphrase}
        />
      </CenteredModal>

      <CenteredModal
        isVisible={passphraseModal}
        onClose={() => {
          setPassphraseModal(false)
        }}
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
  },
});

export default ExportKey;

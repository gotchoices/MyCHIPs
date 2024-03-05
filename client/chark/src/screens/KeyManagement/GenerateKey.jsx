import React, { useState } from "react";
import { useSelector, useDispatch } from "react-redux";
import { View, Text, StyleSheet, Alert } from "react-native";

import Button from "../../components/Button";
import SigningKeyWarning from "../../components/SigningKeyWarning";
import BottomSheetModal from "../../components/BottomSheetModal";

import useSocket from "../../hooks/useSocket";
import { colors, KeyConfig } from "../../config/constants";
import { updatePublicKey } from "../../services/profile";
import {
  storePrivateKey,
  storePublicKey,
} from "../../utils/keychain-store";
import {
  setPrivateKey,
  setPublicKey,
} from "../../redux/profileSlice";
import CenteredModal from "../../components/CenteredModal";
import ExportModal from "../Setting/GenerateKey/ExportModal";
import SuccessContent from "../../components/SuccessContent";
import PassphraseModal from "../Setting/GenerateKey/PassphraseModal";
import GenerateExportModal from "../Setting/GenerateKey/GenerateExportModal";

const GenerateKey = () => {
  const subtle = window.crypto.subtle;
  const dispatch = useDispatch();

  const { wm } = useSocket();
  const { user } = useSelector((state) => state.currentUser);

  const [showGenerateWarning, setShowGenerateWarning] = useState(
    false
  );
  const [generating, setGenerating] = useState(false);

  const [showSuccess, setShowSuccess] = useState(false);
  const [passphrase, setPassphrase] = useState(undefined);
  const [showKeyModal, setShowKeyModal] = useState(false);
  const [passphraseModal, setPassphraseModal] = useState(false);

  const { privateKey } = useSelector((state) => state.profile);

  const user_ent = user?.curr_eid;

  const onGenerateClick = () => {
    setShowGenerateWarning(true);
  };

  const onGenerateCancel = () => {
    setShowGenerateWarning(false);
  };

  const onAccept = async () => {
    try {
      setGenerating(true);
      const keyPair = await subtle.generateKey(KeyConfig, true, [
        "sign",
        "verify",
      ]);

      const publicKey = await subtle.exportKey(
        "jwk",
        keyPair.publicKey
      );
      const privateKey = await subtle.exportKey(
        "jwk",
        keyPair.privateKey
      );

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
      Alert.alert("Error", err.message);
    } finally {
      setGenerating(false);
    }
  };

  return (
    <>
      <View style={{ marginTop: 30 }}>
        <Text style={styles.generate}>generate_text</Text>
        <Text style={styles.description}>
          Generating a new key can be a destructive action. Remember
          to save your current active key by exporting it to a safe
          place.
        </Text>

        <Button
          style={{ marginTop: 16, width: "50%", height: 30 }}
          title="generate_text"
          onPress={onGenerateClick}
        />
      </View>

      <BottomSheetModal
        isVisible={showGenerateWarning}
        onClose={onGenerateCancel}
      >
        <SigningKeyWarning
          onAccept={() => {
            setShowGenerateWarning(false);
            if (privateKey) {
              setPassphraseModal(true);
            } else {
              onAccept();
            }
          }}
          onCancel={onGenerateCancel}
          title="Generating a new key is a destructive action"
          description={`When you open a tally it is signed with a key and needs that key to operate.\n\nIt’s recommended to export and save your keys before you generate new ones.`}
        />
      </BottomSheetModal>



      <CenteredModal
        isVisible={showKeyModal}
        onClose={() => setShowKeyModal(false)}
      >
        <GenerateExportModal
          privateKey={privateKey}
          cancel={() => {
            setPassphrase(undefined);
            setShowKeyModal(false);
          }}
          generateKey={()=>{
            setShowKeyModal(false);
            onAccept()}}
          passphrase={passphrase}
        />
      </CenteredModal>

      <CenteredModal
        isVisible={passphraseModal}
        onClose={() => {
          setPassphraseModal(false);
        }}
      >
        <PassphraseModal
        title='Please export your current key before generating a new one.'
        subTitle='Your key will be encrypted with a passphrase. Store your passphrase in a safe place. You will need it in order to use the exported key.'
          onPassphraseConfirmed={(passphrase) => {
            setPassphrase(passphrase);
            setPassphraseModal(false);
            setShowKeyModal(true);
          }}
          cancel={() => {
            setPassphraseModal(false);
          }}
        />
      </CenteredModal>

      <BottomSheetModal
        isVisible={showSuccess}
        onClose={() => setShowSuccess(false)}
      >
        <SuccessContent
          message="New key has been generated"
          onDone={() => 
            setShowSuccess(false)
          }
          onDismiss={() => 
            setShowSuccess(false)
          }
        />
      </BottomSheetModal>
    </>
  );
};

const styles = StyleSheet.create({
  generate: {
    color: colors.black,
    fontSize: 15,
    fontFamily: "inter",
    fontWeight: "500",
  },
  description: {
    color: colors.gray300,
    fontWeight: "500",
    fontFamily: "inter",
    fontSize: 12,
    lineHeight: 13,
  },
});

export default GenerateKey;

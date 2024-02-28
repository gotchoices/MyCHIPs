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
import GeneratePassphraseModal from "../Setting/GenerateKey/ImportPassphaseModal";
import SuccessContent from "../../components/SuccessContent";

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

  const [privateKey, setPrivateKeyValue] = useState(undefined);

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
      setPrivateKeyValue(strPrivateKey);
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
        <Text style={styles.generate}>Generate</Text>
        <Text style={styles.description}>
          Generating a new key can be a destructive action. Remember
          to save your current active key by exporting it to a safe
          place.
        </Text>

        <Button
          style={{ marginTop: 16, width: "50%", height: 30 }}
          title="Generate"
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
            setPassphraseModal(true);
          }}
          onCancel={onGenerateCancel}
          title="Generating a new key is a destructive action"
          description={`When you open a tally it is signed with a key and needs that key to operate.\n\nIt’s recommended to export and save your keys before you generate new ones.`}
        />
      </BottomSheetModal>

      <CenteredModal
        isVisible={passphraseModal}
        onClose={() => {
          setPassphraseModal(false);
        }}
      >
        <GeneratePassphraseModal
          loading={generating}
          onPassphraseConfirmed={(passphrase) => {
            setPassphrase(passphrase);
            setPassphraseModal(false);
            onAccept();
          }}
          cancel={() => {
            setPassphraseModal(false);
          }}
        />
      </CenteredModal>

      <CenteredModal
        isVisible={showKeyModal}
        onClose={() => setShowKeyModal(false)}
      >
        <ExportModal
          privateKey={privateKey}
          cancel={() => {
            setPassphrase(undefined);
            setShowKeyModal(false);
          }}
          passphrase={passphrase}
        />
      </CenteredModal>

      <BottomSheetModal
        isVisible={showSuccess}
        onClose={() => setShowSuccess(false)}
      >
        <SuccessContent
          message="New key has been generated"
          onDone={() => {
            setShowSuccess(false);
            setShowKeyModal(true);
          }}
          onDismiss={() => {
            setShowSuccess(false);
            setShowKeyModal(true);
          }}
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

import React, { useEffect } from "react";
import {
  Modal,
  View,
  ActivityIndicator,
  StyleSheet,
  Text,
  BackHandler,
} from "react-native";
import { useSelector } from "react-redux";

import useSocket from "../../../../hooks/useSocket";
import {
  storePrivateKey,
  storePublicKey,
} from "../../../../utils/keychain-store";
import { updatePublicKey } from "../../../../services/profile";
import { KeyConfig } from "../../../../config/constants";
import { generateKeyPair, exportKey } from '../../../../services/crypto';

export const GenerateKeysDialog = ({
  visible,
  onDismiss,
  onKeySaved,
  onError,
}) => {
  const { wm } = useSocket();
  const { user } = useSelector((state) => state.currentUser);
  const user_ent = user?.curr_eid;

  const handleBackButtonClick = () => {
    onDismiss();
    return true;
  };

  const storeKeys = (publicKey, privateKey) => {
    updatePublicKey(wm, {
      public_key: publicKey,
      where: {
        user_ent,
      },
    })
      .then(() => {
        return Promise.all([
          storePublicKey(JSON.stringify(publicKey)),
          storePrivateKey(JSON.stringify(privateKey)),
        ]);
      })
      .then(() => {
        onKeySaved();
      })
      .catch((err) => {
        onError(err.message);
      })
      .finally(onDismiss);
  };

  useEffect(() => {
    async function generateKeys() {
      try {
        // Use the crypto service to generate and export keys
        const keyPair = await generateKeyPair(KeyConfig, ["sign", "verify"]);
        const currentKeyPair = {
          publicKey: keyPair.publicKey,
          privateKey: keyPair.privateKey,
        };
        const pubKey = await exportKey(
          "jwk",
          keyPair.publicKey
        );
        const priKey = await exportKey(
          "jwk",
          currentKeyPair.privateKey
        );
        storeKeys(pubKey, priKey);
      } catch (err) {
        onError(err.message);
      } finally {
        onDismiss();
      }
    }

    if (visible) {
      generateKeys();
    }
  }, [visible]);

  return (
    <Modal
      visible={visible}
      transparent={true}
      animationType="fade"
      onDismiss={onDismiss}
      onRequestClose={onDismiss}
    >
      <View style={styles.modalBackground}>
        <View style={styles.activityIndicatorWrapper}>
          <ActivityIndicator size="large" color="#000000" />
          <Text>Generating Keys</Text>
        </View>
      </View>
    </Modal>
  );
};

const styles = StyleSheet.create({
  modalBackground: {
    flex: 1,
    alignItems: "center",
    justifyContent: "center",
    backgroundColor: "rgba(0, 0, 0, 0.5)",
  },
  activityIndicatorWrapper: {
    backgroundColor: "#FFFFFF",
    padding: 20,
    borderRadius: 10,
  },
});

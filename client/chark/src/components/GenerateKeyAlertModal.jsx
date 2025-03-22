import React, { useState } from "react";
import {
  Modal,
  View,
  StyleSheet,
  Text,
  ActivityIndicator,
} from "react-native";
import { useSelector } from "react-redux";
import useSocket from "../hooks/useSocket";
import { updatePublicKey } from "../services/profile";
import {
  storePrivateKey,
  storePublicKey,
} from "../utils/keychain-store";
import Button from "./Button";
import { colors, KeyConfig } from "../config/constants";
import { WarningIcon } from "./SvgAssets/SvgAssets";
import useMessageText from '../hooks/useMessageText';
import { generateKeyPair, exportKey } from '../services/crypto';

export const GenerateKeysAlertModal = ({
  visible,
  onDismiss,
  onKeySaved,
  onError,
}) => {
  const { wm } = useSocket();
  const { user } = useSelector((state) => state.currentUser);
  const user_ent = user?.curr_eid;

  const [isRequesting, setIsRequesting] = useState(false);

  const { messageText } = useMessageText();
  const charkText = messageText?.chark?.msg;

  const closeModal = () => {
    setIsRequesting(false);
    onDismiss();
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
      .finally(closeModal);
  };

  const generateKeys = async () => {
    setIsRequesting(true);
    
    try {
      // Use the crypto service to generate and export keys
      const keyPair = await generateKeyPair(KeyConfig, ["sign", "verify"]);
      const currentKeyPair = {
        publicKey: keyPair.publicKey,
        privateKey: keyPair.privateKey,
      };
      const pubKey = await exportKey("jwk", keyPair.publicKey);
      const priKey = await exportKey(
        "jwk",
        currentKeyPair.privateKey
      );

      storeKeys(pubKey, priKey);
    } catch (err) {
      onError(err.message);
    } finally {
      closeModal();
    }
  };

  return (
    <Modal
      visible={visible}
      transparent={true}
      animationType="fade"
      onDismiss={onDismiss}
      onRequestClose={closeModal}
    >
      <View style={styles.modalBackground}>
        <View style={styles.activityIndicatorWrapper}>
          {isRequesting ? (
            <>
              <View style={styles.iconWrapper}>
                <ActivityIndicator size="large" color="#000000" />
              </View>
              <View style={styles.iconWrapper}>
                <Text style={styles.font}>Generating Keys</Text>
              </View>
            </>
          ) : (
            <>
              <View style={styles.iconWrapper}>
                <WarningIcon size={50} />
              </View>
              <Text
                style={[
                  styles.font,
                  {
                    fontSize: 17,
                    fontWeight: "700",
                    textAlign: "center",
                    paddingBottom: 20,
                  },
                ]}
              >
                {charkText?.keywarn?.title ?? ''}
              </Text>

              <Text style={styles.font}>
                {charkText?.keywarn?.help ?? ''}
              </Text>

              <View style={styles.buttonWrapper}>
                <Button
                  title={charkText?.proceed?.title ?? ''}
                  onPress={generateKeys}
                  textColor={colors.blue2}
                  style={styles.secondaryButton}
                />

                <Button
                  title={charkText?.cancel?.title ?? ''}
                  onPress={onDismiss}
                  style={styles.button}
                />
              </View>
            </>
          )}
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
    left: 0,
    right: 0,
    bottom: 0,
    padding: 20,
    borderRadius: 10,
    position: "absolute",
    backgroundColor: "#FFFFFF",
  },
  buttonWrapper: {
    flex: 1,
    marginVertical: 30,
    flexDirection: "row",
    alignItems: "center",
    justifyContent: "space-between",
  },
  button: {
    backgroundColor: colors.blue2,
    borderColor: colors.blue2,
    width: "45%",
    borderRadius: 40,
    height: 45,
    alignItems: "center",
    justifyContent: "center",
  },
  secondaryButton: {
    backgroundColor: colors.white,
    borderColor: colors.blue2,
    width: "45%",
    borderRadius: 40,
    height: 45,
    alignItems: "center",
    justifyContent: "center",
  },
  iconWrapper: {
    flex: 1,
    marginVertical: 40,
    alignItems: "center",
    justifyContent: "center",
  },
  font: { fontWeight: "500", paddingBottom: 10 },
});

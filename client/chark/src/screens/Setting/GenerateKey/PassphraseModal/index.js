import React, { useState } from "react";

import {
  Alert,
  StyleSheet,
  TextInput,
  View,
  Keyboard,
  Text,
} from "react-native";
import Button from "../../../../components/Button";
import { colors } from "../../../../config/constants";

const PassphraseModal = (props) => {
  const [passprase, setPassphrase] = useState(undefined);
  const [confimrPassprase, setConfirmPassphrase] = useState(
    undefined
  );

  const onConfirmPassphrase = () => {
    if (passprase && confimrPassprase) {
      if (passprase !== confimrPassprase) {
        return Alert.alert("Error", "Your passphrase doesnot match.");
      }

      Keyboard.dismiss();
      props.onPassphraseConfirmed(passprase);
    } else {
      Alert.alert("Error", "Please enter passphrase to continue");
    }
  };

  return (
    <View style={styles.container}>
      <Text style={styles.title}>Export Key</Text>

      <Text style={styles.text}>
        Your key will be encrypted with a passphrase. Store your
        passphrase in a safe place. You will need it in order to use
        the exported key.
      </Text>

      <TextInput
        style={styles.textInput}
        placeholder="Enter Passphrase"
        value={passprase}
        onChangeText={setPassphrase}
        secureTextEntry={true}
      />

      <TextInput
        value={confimrPassprase}
        secureTextEntry={true}
        style={styles.textInput}
        onChangeText={setConfirmPassphrase}
        placeholder="Confirm Passphrase"
      />

      <View style={styles.row}>
        <Button
          style={styles.secondaryButton}
          onPress={props.cancel}
          title="Cancel"
          textColor={colors.blue}
        />

        <Button
          style={{ width: "45%" }}
          onPress={onConfirmPassphrase}
          title="Export"
        />
      </View>
    </View>
  );
};

const styles = StyleSheet.create({
  container: {
    flex: 1,
    paddingTop:10,
    paddingHorizontal:20
  },
  textInput: {
    height: 40,
    borderWidth: 1,
    borderRadius: 6,
    marginVertical: 10,
    paddingVertical: 0,
    paddingHorizontal: 12,
    borderColor: "#BBBBBB",
  },
  row: {
    flex: 1,
    paddingTop: 20,
    flexDirection: "row",
    justifyContent: "space-between",
  },
  secondaryButton: {
    width: "45%",
    marginRight: 20,
    borderColor: colors.blue,
    backgroundColor: colors.white,
  },
  title: {
    fontSize: 16,
    color: '#636363',
    paddingBottom:20,
    textAlign:'center',
    fontWeight: '500'
  },
  text:{
    fontSize: 13,
    color: colors.black,
    paddingBottom:20,

  }
});

export default PassphraseModal;

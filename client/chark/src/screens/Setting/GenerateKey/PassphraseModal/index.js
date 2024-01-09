import React, { useState } from "react";
import { Alert, Button, StyleSheet, TextInput, View, Keyboard } from "react-native"

const PassphraseModal = (props) => {
  const [passprase, setPassphrase] = useState(undefined);

  const onConfirmPassphrase = () => {
    if (passprase) {
      Keyboard.dismiss();
      props.onPassphraseConfirmed(passprase);
    } else {
      Alert.alert("Error", "Please enter passphrase to continue");
    }
  }

  return <View style={styles.container}>
    <TextInput
      style={styles.textInput}
      placeholder="Enter Passphrase"
      value={passprase}
      onChangeText={setPassphrase}
      secureTextEntry={true}
    />
    <View style={styles.row}>
      <Button
        onPress={props.cancel}
        title="Cancel"
      />
      <View style={{ width: 12 }} />
      <Button
        onPress={onConfirmPassphrase}
        title="Confirm Passphrase"
      />
    </View>
  </View>
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
  },
  textInput: {
    marginVertical: 24,
    borderWidth: 1,
    padding: 10,
  },
  row: {
    flexDirection: 'row',
  }
})

export default PassphraseModal;

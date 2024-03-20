import React, { useState } from "react";
import {
  Alert,
  StyleSheet,
  TextInput,
  View,
  Keyboard,
  Text,
  TouchableWithoutFeedback,
} from "react-native";
import Button from "../../../../components/Button";
import PropTypes from 'prop-types'

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

  const onWithoutExport = () => {
    if(props.onWithoutExport) {
      props.onWithoutExport();
    }
  }

  return (
    <View style={styles.container}>
      <Text style={styles.title}>Export Key</Text>

      <Text style={styles.text}>
      {props.title? props.title:  'Your key will be encrypted with a passphrase. Store your passphrase in a safe place. You will need it in order to use the exported key.'}
      </Text>

    {props.subTitle &&
      <Text style={styles.text}>
      {props.subTitle}
      </Text>
    }

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
        {['export', 'import_without'].includes(props.action) && (
          <Button
            style={styles.secondaryButton}
            onPress={props.cancel}
            title="Cancel"
            textColor={colors.blue}
          />
        )}

        {props.action === 'generate' && (
          <Button
            style={styles.secondaryButton}
            onPress={onWithoutExport}
            title="generate_without"
            textColor={colors.blue}
          />
        )}

        {props.action === 'import' && (
          <Button
            style={styles.secondaryButton}
            onPress={onWithoutExport}
            title="import_without"
            textColor={colors.blue}
          />
        )}

        <Button
          style={{ width: "45%" }}
          onPress={onConfirmPassphrase}
          title={props.buttonTitle?props.buttonTitle:"Export"}
        />
      </View>

      {['import', 'generate'].includes(props.action) && (
        <View style={styles.backContainer}>
          <TouchableWithoutFeedback onPress={props.cancel}>
            <Text style={styles.back}>back_text</Text>
          </TouchableWithoutFeedback>
        </View>
      )}
    </View>
  );
};

PassphraseModal.propTypes = {
  action: PropTypes.oneOf(['export', 'generate', 'import', 'import_without']),
  // Function for continuing the action without the export(generate and import)
  onWithoutExport: PropTypes.func,
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
    padding: 20,
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
    paddingVertical: 20,
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

  },
  backContainer: {
    alignItems: 'center',
    justifyContent: 'center',
  },
  back: {
    color: colors.blue,
    fontFamily: 'inter',
    fontWeight: '500',
    fontSize: 14,
  }
});

export default PassphraseModal;

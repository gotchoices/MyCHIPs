import React, { useState } from "react";
import {
  Alert,
  StyleSheet,
  TextInput,
  View,
  Keyboard,
  Text,
} from "react-native";
import Toast from 'react-native-toast-message';
import PropTypes from 'prop-types'

import Button from '../../../../components/Button';
import CustomToast from '../../../../components/Toast';

import { colors, toastVisibilityTime } from "../../../../config/constants";
import useMessageText from "../../../../hooks/useMessageText";
import { getLanguageText } from "../../../../utils/language";

const PassphraseModal = (props) => {
  const [passphrase, setPassphrase] = useState(undefined);
  const [confirmPassphrase, setConfirmPassphrase] = useState(
    undefined
  );
  const [errors, setErrors] = useState(new Set());

  const { messageText } = useMessageText();
  const charkText = messageText?.chark?.msg;

  const onExport = () => {
    try {
      Keyboard.dismiss();
      
      // Check if both passphrase fields are filled
      if (passphrase && confirmPassphrase) {
        // Check if passphrases match
        if (passphrase !== confirmPassphrase) {
          setErrors(prev => new Set(prev).add('passphrase').add('confirmPassphrase'))
          return;
        }

        // If everything is valid, call the callback with the passphrase
        if (props.onPassphraseConfirmed) {
          props.onPassphraseConfirmed(passphrase);
        }
      } 
      // For export action, validate inputs
      else if (props.action === 'export') {
        isInputsValid();
      } 
      // For other actions, check if we can continue without export
      else if (props.onWithoutExport) {
        let isValid = true;
        
        // If either field has a value, validate both
        if (passphrase || confirmPassphrase) {
          isValid = isInputsValid();
        }

        if (!isValid) return;
        props.onWithoutExport();
      }
    } catch (error) {
      console.error("Error in PassphraseModal.onExport:", error);
      Alert.alert("Error", "An error occurred. Please try again.");
    }
  }

  const removeErrors = () => {
    setErrors(new Set());
  }

  const isInputsValid = () => {
    if(!passphrase && !confirmPassphrase) {
      setErrors(prev => new Set().add('passphrase').add('confirmPassphrase'))
      return false
    } else if(passphrase && !confirmPassphrase) {
      setErrors(prev => new Set().add('confirmPassphrase'))
      return false
    } else if(!passphrase && confirmPassphrase) {
      setErrors(prev => new Set().add('passphrase'))
      return false
    }

    return true; 
  }


  return (
    <View style={styles.container}>
      <Text style={styles.title}>
        {props.title || (props.action === 'export' ? getLanguageText(charkText, 'export') : '')}
      </Text>

      <Text style={styles.text}>
        {props.subTitle || getLanguageText(charkText, 'keypass', 'help')}
      </Text>

      <TextInput
        style={[styles.textInput, errors.has('passphrase') ? styles.errorInput : {}]}
        placeholder="Enter Passphrase"
        value={passphrase}
        onChangeText={setPassphrase}
        onFocus={removeErrors}
        secureTextEntry={true}
      />

      <TextInput
        value={confirmPassphrase}
        secureTextEntry={true}
        style={[styles.textInput, errors.has('confirmPassphrase') ? styles.errorInput : {}]}
        onChangeText={setConfirmPassphrase}
        placeholder="Confirm Passphrase"
        onFocus={removeErrors}
      />

      <View style={styles.row}>
        <Button
          style={styles.secondaryButton}
          onPress={props.cancel}
          title={getLanguageText(charkText, 'cancel')}
          textColor={colors.blue}
        />

        <Button
          style={{ width: "45%" }}
          onPress={onExport}
          title={props?.buttonTitle || (props.action === 'export' ? getLanguageText(charkText, 'export') : 'Submit')}
        />
      </View>

      <CustomToast />
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
  errorInput: {
    borderColor: colors.red,
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

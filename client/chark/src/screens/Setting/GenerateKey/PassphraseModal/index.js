import React, { useState, useEffect } from "react";
import {
  Alert,
  StyleSheet,
  TextInput,
  View,
  Keyboard,
  Text,
  TouchableOpacity,
} from "react-native";
import Toast from 'react-native-toast-message';
import PropTypes from 'prop-types';

import Button from '../../../../components/Button';
import CustomToast from '../../../../components/Toast';
import EyeIcon from '../../../../../assets/svg/eye_icon.svg';

import { colors, toastVisibilityTime } from "../../../../config/constants";
import useMessageText from "../../../../hooks/useMessageText";
import { getLanguageText } from "../../../../utils/language";

const PassphraseModal = (props) => {
  const [passphrase, setPassphrase] = useState(undefined);
  const [confirmPassphrase, setConfirmPassphrase] = useState(
    undefined
  );
  const [errors, setErrors] = useState(new Set());
  // Track if the button should be enabled
  const [isButtonEnabled, setIsButtonEnabled] = useState(false);
  // Track password visibility
  const [isPassphraseVisible, setIsPassphraseVisible] = useState(false);
  const [isConfirmPassphraseVisible, setIsConfirmPassphraseVisible] = useState(false);

  const { messageText } = useMessageText();
  const charkText = messageText?.chark?.msg;
  
  // Effect to check if the button should be enabled
  useEffect(() => {
    // For import_without action, only need one passphrase
    if (props.action === 'import_without') {
      setIsButtonEnabled(!!passphrase);
    } 
    // For export and other actions that need both fields
    else {
      // Both fields must be filled and match
      setIsButtonEnabled(
        !!passphrase && 
        !!confirmPassphrase && 
        passphrase === confirmPassphrase
      );
    }
  }, [passphrase, confirmPassphrase, props.action]);

  const onExport = () => {
    try {
      Keyboard.dismiss();
      
      // For import_without action, only need one passphrase field and no confirmation
      if (props.action === 'import_without') {
        if (!passphrase) {
          setErrors(prev => new Set(prev).add('passphrase'));
          return;
        }
        
        // For decryption, just pass the single passphrase
        if (props.onPassphraseConfirmed) {
          props.onPassphraseConfirmed(passphrase);
          return;
        }
      }
      
      // Check if both passphrase fields are filled for regular cases
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
        {props.title || 
          (props.action === 'export' ? getLanguageText(charkText, 'export') :
           props.action === 'import_without' ? getLanguageText(charkText, 'import', 'title') : '')}
      </Text>

      <Text style={styles.text}>
        {props.subTitle || 
          (props.action === 'import_without' ? 
            getLanguageText(charkText, 'import', 'help') : 
            getLanguageText(charkText, 'keypass', 'help'))}
      </Text>

      <View style={[
        styles.inputContainer,
        errors.has('passphrase') ? styles.errorContainer : {}
      ]}>
        <TextInput
          style={[
            styles.textInput, 
            { flex: 1 }
          ]}
          placeholder={props.action === 'import_without' ? "Enter Decryption Passphrase" : "Enter Passphrase"}
          value={passphrase}
          onChangeText={setPassphrase}
          onFocus={removeErrors}
          secureTextEntry={!isPassphraseVisible}
        />
        <TouchableOpacity 
          style={styles.eyeIconContainer} 
          onPress={() => setIsPassphraseVisible(!isPassphraseVisible)}
        >
          <EyeIcon width={20} height={20} color={colors.blue} />
        </TouchableOpacity>
      </View>

      {/* Only show confirm passphrase field for non-import_without actions */}
      {props.action !== 'import_without' && (
        <View style={[
          styles.inputContainer,
          errors.has('confirmPassphrase') ? styles.errorContainer : {}
        ]}>
          <TextInput
            value={confirmPassphrase}
            secureTextEntry={!isConfirmPassphraseVisible}
            style={[
              styles.textInput, 
              { flex: 1 }
            ]}
            onChangeText={setConfirmPassphrase}
            placeholder="Confirm Passphrase"
            onFocus={removeErrors}
          />
          <TouchableOpacity 
            style={styles.eyeIconContainer}
            onPress={() => setIsConfirmPassphraseVisible(!isConfirmPassphraseVisible)}
          >
            <EyeIcon width={20} height={20} color={colors.blue} />
          </TouchableOpacity>
        </View>
      )}

      <View style={styles.row}>
        <Button
          style={styles.secondaryButton}
          onPress={props.cancel}
          title={getLanguageText(charkText, 'cancel')}
          textColor={colors.blue}
        />

        <Button
          style={{ 
            width: "45%", 
            opacity: isButtonEnabled ? 1 : 0.5 
          }}
          disabled={!isButtonEnabled}
          onPress={onExport}
          title={props?.buttonTitle || 
            (props.action === 'export' ? getLanguageText(charkText, 'export') : 
             props.action === 'import_without' ? getLanguageText(charkText, 'import') : 'Submit')}
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
  inputContainer: {
    flexDirection: 'row',
    alignItems: 'center',
    marginVertical: 10,
    borderWidth: 1,
    borderRadius: 6,
    borderColor: "#BBBBBB",
    height: 40,
  },
  textInput: {
    height: 40,
    paddingVertical: 0,
    paddingHorizontal: 12,
    borderWidth: 0,
  },
  errorContainer: {
    borderColor: colors.red,
  },
  eyeIconContainer: {
    padding: 10,
    justifyContent: 'center',
    alignItems: 'center',
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

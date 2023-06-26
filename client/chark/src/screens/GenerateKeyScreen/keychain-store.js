import * as Keychain from 'react-native-keychain';
import ReactNativeBiometrics, { BiometryTypes } from 'react-native-biometrics'

const rnBiometrics = new ReactNativeBiometrics()

const isBiometricsAvailable = () => {
  return new Promise((resolve, reject) => {
    rnBiometrics.isSensorAvailable()
      .then((result) => {
        const { available, biometryType, error } = result;
        if (available) {
          return rnBiometrics.simplePrompt({
            promptMessage: 'Confirm biometrics to store keys'
          });
        } else if (error === 'BIOMETRIC_ERROR_NONE_ENROLLED') {
          reject('Biometrics not enrolled');
        } else {
          reject('Biometrics not supported');
        }
      })
      .then(result => resolve(result))
      .catch(error => reject(error.toString()));
  })
}

/** 
 * accessControl: Keychain.ACCESS_CONTROL.BIOMETRY_CURRENT_SET_OR_DEVICE_PASSCODE,
 * on iOS 11 and above if biometrics no set then will be promted to device pincode
 * on android however the result may be different based on different android version for phones
 * */
export const storeKey = (key) => {
  return new Promise((resolve, reject) => {
    isBiometricsAvailable()
      .then(result => {
        const { success, error } = result;
        if (success) {
          return Keychain.setGenericPassword('private_key', key, {
            service: 'private_key',
            accessControl: Keychain.ACCESS_CONTROL.BIOMETRY_CURRENT_SET_OR_DEVICE_PASSCODE, // all 
            accessible: Keychain.ACCESSIBLE.WHEN_PASSCODE_SET_THIS_DEVICE_ONLY, // ios
            authenticationType: Keychain.AUTHENTICATION_TYPE.DEVICE_PASSCODE_OR_BIOMETRICS, // ios
            securityLevel: Keychain.SECURITY_LEVEL.SECURE_SOFTWARE, // requires for the key to be stored in the Android Keystore
            storage: Keychain.STORAGE_TYPE.RSA, //Encryption with biometrics.
          });
        } else {
          reject(error.toString());
        }
      })
      .then(result => resolve(result))
      .catch(error => reject(error.toString()));
  })
};

export const retrieveKey = (service) => {
  return new Promise((resolve, reject) => {
    try {
      Keychain.getGenericPassword({ service: service })
        .then(resolve)
        .catch(reject);
    } catch (error) {
      reject(error);
    }
  })
};

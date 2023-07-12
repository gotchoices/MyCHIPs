import * as Keychain from 'react-native-keychain';
import ReactNativeBiometrics, { BiometryTypes } from 'react-native-biometrics'
import { keyServices } from '../config/constants';

const rnBiometrics = new ReactNativeBiometrics()

const isBiometricsAvailable = () => {
  return rnBiometrics.isSensorAvailable()
    .then((result) => {
      const { available, biometryType, error } = result;
      if (available) {
        return { success: true };
        // return rnBiometrics.simplePrompt({
        //   promptMessage: 'Confirm biometrics to store keys'
        // });
      } else if (error === 'BIOMETRIC_ERROR_NONE_ENROLLED') {
        throw new Error('Biometrics not enrolled')
      } else {
        throw new Error('Biometrics not supported')
      }
    })
}

/** 
 * accessControl: Keychain.ACCESS_CONTROL.BIOMETRY_CURRENT_SET_OR_DEVICE_PASSCODE,
 * on iOS 11 and above if biometrics no set then will be promted to device pincode
 * on android however the result may be different based on different android version for phones
 * */
export const storePrivateKey = (key) => {
  return isBiometricsAvailable()
    .then(result => {
      const { success, error } = result;
      if (success) {
        return Keychain.setGenericPassword('private_key', key, {
          service: keyServices.privateKey,
          accessControl: Keychain.ACCESS_CONTROL.BIOMETRY_CURRENT_SET_OR_DEVICE_PASSCODE, // all 
          accessible: Keychain.ACCESSIBLE.WHEN_PASSCODE_SET_THIS_DEVICE_ONLY, // ios
          authenticationType: Keychain.AUTHENTICATION_TYPE.DEVICE_PASSCODE_OR_BIOMETRICS, // ios
          securityLevel: Keychain.SECURITY_LEVEL.SECURE_SOFTWARE, // requires for the key to be stored in the Android Keystore
          storage: Keychain.STORAGE_TYPE.RSA, //Encryption with biometrics.
        });
      } else {
        console.log('err', error)
      }
    })
};

export const storePublicKey = (key) => {
  return Keychain.setGenericPassword('public_key', key, {
    service: keyServices.publicKey,
    securityLevel: Keychain.SECURITY_LEVEL.SECURE_SOFTWARE, // requires for the key to be stored in the Android Keystore
  });
}

export const retrieveKey = (service) => {
  return Keychain.getGenericPassword({ service: service })
};

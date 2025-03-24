import * as Keychain from 'react-native-keychain';
import ReactNativeBiometrics, { BiometryTypes } from 'react-native-biometrics'
import { keyServices } from '../config/constants';
import DeviceInfo from 'react-native-device-info';

const rnBiometrics = new ReactNativeBiometrics()
const isBiometricsAvailable = () => {
  // Always bypass biometrics on emulators/simulators for both Android and iOS
  if (DeviceInfo.isEmulator()) {
    console.log('Running on emulator/simulator - bypassing biometrics check');
    return Promise.resolve({ success: true });
  }
  
  return rnBiometrics.isSensorAvailable()
    .then((result) => {
      const { available, biometryType, error } = result;
      
      if (available) {
        // Sensor is available and can be used
        return { success: true };
      } else if (error === 'BIOMETRIC_ERROR_NONE_ENROLLED') {
        // User hasn't enrolled biometrics on their device
        throw new Error('Biometrics not enrolled');
      } else {
        // Hardware doesn't support biometrics or other error
        throw new Error('Biometrics not supported');
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
        let options = {
          service: keyServices.privateKey,
        }

        if (!DeviceInfo.isEmulator()) {
          // Only apply biometric security options on real devices
          const _options = {
            accessControl: Keychain.ACCESS_CONTROL.BIOMETRY_CURRENT_SET_OR_DEVICE_PASSCODE, // all 
            accessible: Keychain.ACCESSIBLE.WHEN_PASSCODE_SET_THIS_DEVICE_ONLY, // ios
            authenticationType: Keychain.AUTHENTICATION_TYPE.DEVICE_PASSCODE_OR_BIOMETRICS, // ios
            securityLevel: Keychain.SECURITY_LEVEL.SECURE_SOFTWARE, // requires for the key to be stored in the Android Keystore
            storage: Keychain.STORAGE_TYPE.RSA, //Encryption with biometrics.
          }

          options = {
            ...options,
            ..._options,
          }
        } else {
          console.log('Using simplified keychain options for emulator/simulator');
        }
        
        return Keychain.setGenericPassword('private_key', key, options);
      } else if (error) {
        console.log('Biometrics error:', error);
        // Return a rejected promise with the error
        return Promise.reject(error);
      } else {
        console.log('Unexpected biometrics result:', result);
        return Promise.reject(new Error('Biometrics check failed'));
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

export const isKeyStored = async () => {
  try {
    const privateCreds = await retrieveKey(keyServices.privateKey);
    if (privateCreds) {
      return { keyStored: true, message: "Keys already exist, are you sure you want to override with new keys?" };
    }
    return { keyStored: false };
  } catch (ex) {
    console.log("EXCEPTION ==> ", ex);
    return { keyStored: false };
  }
}

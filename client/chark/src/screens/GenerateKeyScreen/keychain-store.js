import * as Keychain from 'react-native-keychain';

export const storeKey = (key) => {
  return new Promise((resolve, reject) => {
    try {
      Keychain.getSupportedBiometryType().then(supportedType => {
        if (supportedType) {
          Keychain.setGenericPassword('private_key', key, {
            service: 'private_key',
            accessControl: Keychain.ACCESS_CONTROL.BIOMETRY_CURRENT_SET_OR_DEVICE_PASSCODE,
            accessible: Keychain.ACCESSIBLE.WHEN_PASSCODE_SET_THIS_DEVICE_ONLY,
            securityLevel: Keychain.SECURITY_LEVEL.SECURE_SOFTWARE,
            storage: Keychain.STORAGE_TYPE.RSA,
          }).then(result => resolve(result)).catch(reject);
        } else {
          reject("Biometrics not supported");
        }
      });
    } catch (error) {
      reject(error);
    }
  })
};

export const retrieveKey = (service) => {
  return new Promise((resolve, reject) => {
    try {
      Keychain.getGenericPassword({ service: service }).then(resolve).catch(reject);
    } catch (error) {
      reject(error);
    }
  })
};

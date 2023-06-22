import * as Keychain from 'react-native-keychain';

export const storeKey = async (key) => {
  try {
    await Keychain.setGenericPassword('private_key', key, {
      service: 'private_key',
      accessControl: Keychain.ACCESS_CONTROL.BIOMETRY_CURRENT_SET_OR_DEVICE_PASSCODE,
      accessible: Keychain.ACCESSIBLE.WHEN_PASSCODE_SET_THIS_DEVICE_ONLY,
      securityLevel: Keychain.SECURITY_LEVEL.SECURE_SOFTWARE,
      storage: Keychain.STORAGE_TYPE.RSA,
    });
    console.log('Key stored successfully.');
  } catch (error) {
    console.error('Failed to store key:', error);
  }
};


export const retrieveKey = async () => {
  try {
    const credentials = await Keychain.getGenericPassword({ service: 'private_key' });
    if (credentials) {
      console.log('Retrieved key:', credentials);
    } else {
      console.log('No key stored.');
    }
  } catch (error) {
    console.error('Failed to retrieve key:', error);
  }
};

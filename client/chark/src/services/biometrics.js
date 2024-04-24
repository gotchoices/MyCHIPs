import ReactNativeBiometrics from 'react-native-biometrics';
import {BiometricsMismatchError} from '../utils/Errors';

export const promptBiometrics = (message) => {
  const rnBiometrics = new ReactNativeBiometrics();

  return new Promise((resolve, reject) => {
    rnBiometrics.isSensorAvailable().then(result => {
      const { available, error } = result;
      if (available) {
        rnBiometrics.simplePrompt({
          promptMessage: message,
        }).then(res => {
          if (res.success) {
            resolve();
          } else {
            reject(new Error('Biometrics did not match.'));
          }
        }).catch(err => {
          if (err instanceof BiometricsMismatchError) {
            reject(new Error('Biometrics did not match.'));
          } else {
            reject(new Error('Biometrics failed'));
          }
        });
      } else {
        resolve(); // No biometric sensor available
      }
    }).catch(err => {
      reject(new Error('Error checking biometric sensor availability'));
    });
  });
};
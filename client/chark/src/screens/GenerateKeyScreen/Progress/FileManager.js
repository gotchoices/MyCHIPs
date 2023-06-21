import SensitiveInfo from 'react-native-sensitive-info';
import ReactNativeFS from 'react-native-fs';
import CryptoJS from 'react-native-crypto-js';

const PASSPHRASE_KEY = 'passphrase';

// Function to save the passphrase
export const savePassphrase = async (passphrase) => {
  try {
    await SensitiveInfo.setItem(PASSPHRASE_KEY, passphrase, {});
    console.log('Passphrase saved successfully!');
  } catch (error) {
    console.log('Error saving the passphrase:', error);
  }
};

// Function to retrieve the passphrase
export const getPassphrase = async () => {
  try {
    const passphrase = await SensitiveInfo.getItem(PASSPHRASE_KEY, {});
    return passphrase;
  } catch (error) {
    console.log('Error retrieving the passphrase:', error);
    return null;
  }
};

// Function to encrypt the JSON string
const encryptJSON = (jsonString, passphrase) => {
  const encrypted = CryptoJS.AES.encrypt(jsonString, passphrase).toString();
  return encrypted;
};

// Function to decrypt the JSON string
const decryptJSON = (encryptedString, passphrase) => {
  const decryptedBytes = CryptoJS.AES.decrypt(encryptedString, passphrase);
  const decrypted = decryptedBytes.toString(CryptoJS.enc.Utf8);
  return decrypted;
};

// Function to save the encrypted JSON to the file
const saveEncryptedJSONToFile = async (encryptedJSON) => {
  try {
    const downloadsDir = ReactNativeFS.DownloadDirectoryPath;
    const filePath = `${downloadsDir}/data.json`;

    // Write the encrypted JSON to the file
    await ReactNativeFS.writeFile(filePath, encryptedJSON, 'utf8');
    console.log('File saved successfully!');
    return filePath;
  } catch (error) {
    console.log('Error saving the file:', error);
    return null;
  }
};

// Function to open the file with biometrics or passphrase verification
export const openFile = async () => {
  const filePath = `${ReactNativeFS.DownloadDirectoryPath}/data.json`;

  // Check if biometrics are supported on the device
  const isSupported = await SensitiveInfo.isSupported();

  if (isSupported) {
    try {
      // Use biometrics for verification
      const result = await SensitiveInfo.authenticateBiometric('Biometric verification');
      if (result) {
        // Biometric authentication successful, decrypt and open the file
        const savedPassphrase = await getPassphrase();
        if (savedPassphrase) {
          const encryptedData = await ReactNativeFS.readFile(filePath, 'utf8');
          const decryptedData = decryptJSON(encryptedData, savedPassphrase);
          console.log('Decrypted data:', decryptedData);
          // Additional handling to use the decrypted data
        }
      }
    } catch (error) {
      console.log('Biometric authentication error:', error);
      // Additional error handling
    }
  } else {
    // Biometrics not supported, use passphrase verification
    try {
      const savedPassphrase = await getPassphrase();
      if (savedPassphrase) {
        // Prompt the user to enter the passphrase
        // You can implement a passphrase input UI here
        const enteredPassphrase = 'user-entered-passphrase'; // Replace with the user's entered passphrase

        // Check if the entered passphrase matches the saved passphrase
        const isPassphraseValid = await isPassphraseValid(enteredPassphrase);
        if (isPassphraseValid) {
          const encryptedData = await ReactNativeFS.readFile(filePath, 'utf8');
          const decryptedData = decryptJSON(encryptedData, savedPassphrase);
          console.log('Decrypted data:', decryptedData);
          // Additional handling to use the decrypted data
        } else {
          console.log('Incorrect passphrase');
          // Additional handling for incorrect passphrase
        }
      } else {
        console.log('No passphrase saved');
        // Additional handling for no saved passphrase
      }
    } catch (error) {
      console.log('Passphrase verification error:', error);
      // Additional error handling
    }
  }
};

// Function to save the JSON data securely
export const saveSecureJSONToFile = async (jsonString, passphrase) => {
  const encryptedJSON = encryptJSON(jsonString, passphrase);
  const filePath = await saveEncryptedJSONToFile(encryptedJSON);
  return filePath;
};

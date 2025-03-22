import ReactNativeFS from 'react-native-fs';
import Share from 'react-native-share';
import { Platform, Alert } from 'react-native';
import { Buffer } from '@craftzdog/react-native-buffer';
import { deriveKey, encrypt, decrypt } from '../services/crypto';

const getDateTime = () => {
  const currentDate = new Date();
  const year = currentDate.getFullYear().toString();
  const month = String(currentDate.getMonth() + 1).padStart(2, '0');
  const date = String(currentDate.getDate()).padStart(2, '0');
  const hours = String(currentDate.getHours()).padStart(2, '0');
  const minutes = String(currentDate.getMinutes()).padStart(2, '0');
  const seconds = String(currentDate.getSeconds()).padStart(2, '0');
  return `${year}-${month}-${date} ${hours}${minutes}${seconds}`;
}

// Android Support Only
export const downloadJSONFile = (jsonString) => {
  return new Promise((resolve, reject) => {
    const cachedPath = `${ReactNativeFS.CachesDirectoryPath}/key-${getDateTime()}.json`;
    const downloadPath = `${ReactNativeFS.DownloadDirectoryPath}/key-${getDateTime()}.json`;

    ReactNativeFS.writeFile(cachedPath, jsonString, 'utf8')
      .then(() => ReactNativeFS.moveFile(cachedPath, downloadPath))
      .then(() => ReactNativeFS.scanFile(downloadPath))
      .then((result) => resolve(result))
      .catch(err => reject(err));
  });
}

export const shareJSONFile = (jsonString) => {
  return new Promise((resolve, reject) => {
    const cachedPath = `${Platform.OS === 'android' ? "file://" : ''}${ReactNativeFS.TemporaryDirectoryPath}/key-${getDateTime()}.json`;
    const options = {
      title: 'Private Keys',
      url: cachedPath,
      type: 'application/json'
    };

    ReactNativeFS
      .writeFile(cachedPath, jsonString, 'utf8').then(() => Share.open(options))
      .then((result) => resolve(result))
      .catch(err => reject(err));
  });
}

// Android Support Only
export const downloadQRCode = (uri) => {
  return new Promise((resolve, reject) => {
    const baseDownloadPath = ReactNativeFS.DownloadDirectoryPath;
    const downloadPath = baseDownloadPath + `/key-${getDateTime()}.png`;
    ReactNativeFS.moveFile(uri, downloadPath)
      .then(() => ReactNativeFS.scanFile(downloadPath))
      .then((result) => resolve(result))
      .catch(err => {
        reject(err)
      });
  });
}

export const shareQRCode = (uri) => {
  return new Promise((resolve, reject) => {
    const options = {
      title: 'Private Keys',
      url: uri,
    };

    Share.open(options)
      .then((result) => resolve(result))
      .catch(err => reject(err));
  });
}

// We'll now use the centralized crypto service's deriveKey function

// Function to encrypt the JSON string
export const encryptJSON = async (jsonString, passphrase) => {
  try {
    // Add defensive checks
    if (!jsonString) {
      return { success: false, error: "No data to encrypt" };
    }
    
    // Ensure passphrase is a string
    if (!passphrase || typeof passphrase !== 'string') {
      return { success: false, error: "Invalid passphrase" };
    }
    
    // Ensure jsonString is a string
    const stringToEncrypt = typeof jsonString === 'string' ? jsonString : JSON.stringify(jsonString);
    
    // Generate random IV (initialization vector)
    let iv = crypto.getRandomValues(new Uint8Array(12));
    
    // Use the crypto service to derive a key and encrypt
    const [key, salt] = await deriveKey(passphrase);
    const { ciphertext } = await encrypt(stringToEncrypt, key, iv);
    
    // Format the encrypted data
    const encryptedData = JSON.stringify({
      signkey: {
        s: Buffer.from(salt).toString('hex'),
        i: Buffer.from(iv).toString('hex'),
        d: Buffer.from(ciphertext).toString('base64')
      }
    });
    
    return { success: true, data: encryptedData };
  } catch (e) {
    console.error("Encryption error:", e);
    
    // Provide more specific error message based on the error type
    let errorMessage = e.toString();
    if (errorMessage.includes('Web Crypto API not available') || 
        errorMessage.includes('subtle is not a function')) {
      errorMessage = 'Encryption service is not properly initialized. Please restart the app and try again.';
    }
    
    // Alert the user with a friendly error message
    Alert.alert('Export Error', errorMessage);
    
    return { success: false, error: errorMessage };
  }
};

// Function to decrypt the JSON string
export const decryptJSON = async (encryptedString, passphrase) => {
  return new Promise((resolve, reject) => {
    try {
      // Validate inputs
      if (!encryptedString || typeof encryptedString !== 'string') {
        return reject('Invalid encrypted data');
      }
      
      if (!passphrase || typeof passphrase !== 'string') {
        return reject('Invalid passphrase');
      }
      
      // Parse the encrypted data
      let { s, i, d } = JSON.parse(encryptedString).signkey;
      const salt = Buffer.from(s, 'hex');
      const iv = Buffer.from(i, 'hex');
      const data = Buffer.from(d, 'base64');
      
      // Use the crypto service to derive a key and decrypt
      deriveKey(passphrase, salt)
        .then(([key]) => key)
        .then(key => decrypt(data, key, iv))
        .then(bufferData => Buffer.from(new Uint8Array(bufferData)).toString())
        .then(privateKey => resolve(privateKey))
        .catch(e => {
          console.error('Decryption error:', e);
          
          // Provide user-friendly error message
          let errorMessage = e.toString();
          if (errorMessage.includes('Web Crypto API not available') || 
              errorMessage.includes('subtle is not a function')) {
            errorMessage = 'Decryption service is not properly initialized. Please restart the app and try again.';
          } else if (errorMessage.includes('decrypt operation failed')) {
            errorMessage = 'Invalid passphrase or corrupted data';
          }
          
          reject(errorMessage);
        });
    } catch (e) {
      console.error('Exception in decryptJSON:', e);
      reject(e.toString());
    }
  });
};

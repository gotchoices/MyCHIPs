import ReactNativeFS from 'react-native-fs';
import CryptoJS from "react-native-crypto-js";

export const downloadJSONFile = (jsonString) => {
  return new Promise((resolve, reject) => {
    const downloadPath = ReactNativeFS.DownloadDirectoryPath + '/key1.json';

    ReactNativeFS.writeFile(downloadPath, jsonString, 'utf8')
      .then(() => {
        ReactNativeFS.scanFile(downloadPath).then((result) => {
          resolve(result);
        });
      })
      .catch(err => {
        reject(err);
      });
  });
}

export const downloadQRCode = (uri) => {
  return new Promise((resolve, reject) => {
    const downloadPath = ReactNativeFS.DownloadDirectoryPath + '/key.png';
    ReactNativeFS.moveFile(uri, downloadPath)
      .then(() => {
        ReactNativeFS.scanFile(downloadPath).then((result) => {
          resolve(result);
        });
      }).catch(err => {
        reject(err)
      });
  });
}

// Function to encrypt the JSON string
export const encryptJSON = (jsonString, passphrase) => {
  const encrypted = CryptoJS.AES.encrypt(jsonString, passphrase).toString();
  return encrypted;
};

// Function to decrypt the JSON string
export const decryptJSON = async (encryptedString, passphrase) => {
  return new Promise((resolve, reject) => {
    try {
      const decryptedBytes = CryptoJS.AES.decrypt(encryptedString, passphrase);
      const decrypted = decryptedBytes.toString(CryptoJS.enc.Utf8);
      resolve(decrypted);
    } catch (error) {
      console.log("Failed to decrypt ", error);
      reject("Error failed to fetch data");
    }
  });
};

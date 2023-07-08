import ReactNativeFS from 'react-native-fs';
import CryptoJS from "react-native-crypto-js";
import Share from 'react-native-share';
import { Platform } from 'react-native';

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
    const baseDownloadPath = ReactNativeFS.DownloadDirectoryPath;
    const downloadPath = `${baseDownloadPath}/key-${getDateTime()}.json`;

    ReactNativeFS.writeFile(cachedPath, jsonString, 'utf8')
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
      reject(`Error failed to decrept data ${error}`);
    }
  });
};

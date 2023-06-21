import ReactNativeFS from 'react-native-fs';
import CryptoJS from 'react-native-crypto-js';

export const writeFileToDownloads = async (jsonString) => {
  return new Promise((resolve, reject) => {
    const path = ReactNativeFS.DownloadDirectoryPath + '/key.json';
    console.log("File Path ==> ", path);

    ReactNativeFS.writeFile(path, jsonString, 'utf8')
      .then((success) => {
        console.log("Saved ==> ", success);
        resolve(success)
      })
      .catch((err) => {
        console.log("Error==>", err);
        reject(err);
      });
  })
}

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

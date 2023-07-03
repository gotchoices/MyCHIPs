import ReactNativeFS from 'react-native-fs';
import CryptoJS from "react-native-crypto-js";
import { Platform } from 'react-native';
import { CameraRoll } from '@react-native-camera-roll/camera-roll';
import 'react-native-get-random-values';
import { Buffer } from 'buffer';

const subtle = window.crypto.subtle;

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

const iospath = "/Users/insightworkshop/Library/Developer/CoreSimulator/Devices/F7915F4B-6E61-46D0-AFDC-52B8EC9D8BFA/data/Containers/Shared/AppGroup/4F1DADD5-C6A3-429B-AD1C-4B5C74432C3D/File\ Provider\ Storage/Documents";

export const downloadJSONFile = (jsonString) => {
  return new Promise((resolve, reject) => {
    const cachedPath = `${ReactNativeFS.CachesDirectoryPath}/key-${getDateTime()}.json`;
    const baseDownloadPath = Platform.OS === 'ios' ? ReactNativeFS.DocumentDirectoryPath : ReactNativeFS.DownloadDirectoryPath;
    const downloadPath = `${baseDownloadPath}/key-${getDateTime()}.json`;

    console.log("Final Download ", downloadPath);
    ReactNativeFS.writeFile(cachedPath, jsonString, 'utf8')
      .then(() => ReactNativeFS.copyFile(cachedPath, downloadPath))
      .then(() => {
        if (Platform.OS === 'ios') {
          return "File Downloaded";
        } else {
          return ReactNativeFS.scanFile(downloadPath)
        }
      })
      .then((result) => resolve(result))
      .catch(err => reject(err));
  });
}

export const downloadQRCode = (uri) => {
  return new Promise((resolve, reject) => {
    const baseDownloadPath = Platform.OS === 'ios' ? ReactNativeFS.DocumentDirectoryPath : ReactNativeFS.DownloadDirectoryPath;
    const downloadPath = baseDownloadPath + `/key-${getDateTime()}.png`;

    if (Platform.OS === 'ios') {
      CameraRoll.save(uri).then((result) => resolve(result)).catch(ex => reject(ex));
    } else {
      ReactNativeFS.moveFile(uri, downloadPath)
        .then(() => ReactNativeFS.scanFile(downloadPath))
        .then((result) => resolve(result))
        .catch(err => {
          reject(err)
        });
    }
  });
}

const deriveKey = async (password, salt_1) => {
  let salt = salt_1 || crypto.getRandomValues(new Uint8Array(8));
  const importedKey = await subtle.importKey("raw", Buffer.from(password), { name: "PBKDF2" }, false, ["deriveKey"]);
  const key = await subtle.deriveKey(
    { name: "PBKDF2", salt: salt, iterations: 10000, hash: "SHA-256" },
    importedKey,
    { name: 'AES-GCM', length: 256 },
    true,
    ["encrypt", "decrypt"],
  );
  return [key, salt];
};

// Function to encrypt the JSON string
export const encryptJSON = async (jsonString, passphrase) => {
  try {
    let iv = crypto.getRandomValues(new Uint8Array(12));
    let data = Buffer.from(jsonString);
    const [key, salt] = await deriveKey(passphrase);
    const ciphertext = await subtle.encrypt({ name: "AES-GCM", iv }, key, data);
    const encryptedData = JSON.stringify({
      s: Buffer.from(salt).toString('hex'),
      i: Buffer.from(iv).toString('hex'),
      d: Buffer.from(ciphertext).toString('base64')
    });
    return encryptedData;
  } catch (e) {
    return e.toString();
  }
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


/* 
    // const encrypted = CryptoJS.AES.encrypt(jsonString, passphrase).toString();
*/
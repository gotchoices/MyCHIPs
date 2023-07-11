import ReactNativeFS from 'react-native-fs';
import Share from 'react-native-share';
import { Platform } from 'react-native';
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

const deriveKey = async (password, currentSalt) => {
  let salt = currentSalt || crypto.getRandomValues(new Uint8Array(8));
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
    // NOTE: Key may change in future.
    const encryptedData = JSON.stringify({
      sign: {
        s: Buffer.from(salt).toString('hex'),
        i: Buffer.from(iv).toString('hex'),
        d: Buffer.from(ciphertext).toString('base64')
      }
    });
    return { success: true, data: encryptedData };
  } catch (e) {
    return { success: false, error: e };
  }
};

// Function to decrypt the JSON string
export const decryptJSON = async (encryptedString, passphrase) => {
  return new Promise((resolve, reject) => {
    try {
      let { s, i, d } = JSON.parse(encryptedString).sign;
      const salt = Buffer.from(s, 'hex');
      const iv = Buffer.from(i, 'hex');
      const data = Buffer.from(d, 'base64');
      deriveKey(passphrase, salt)
        .then(([key]) => key)
        .then(key => subtle.decrypt({ name: "AES-GCM", iv }, key, data))
        .then(bufferData => Buffer.from(new Uint8Array(bufferData)).toString())
        .then(privateKey => resolve(privateKey))
        .catch(e => reject(JSON.stringify(e)));
    } catch (e) {
      reject(e.toString());
    }
  });
};

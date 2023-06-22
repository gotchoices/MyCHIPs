import SInfo from "react-native-sensitive-info";
import { decryptJSON, encryptJSON } from '../../utils/file-manager';

const key = "UserPrivateKey";
const prefName = 'MychipsKey';
const keychainService = 'MychipsKeychainService';

export const saveKey = async () => {
  try {
    const encryptedValue = encryptJSON(JSON.stringify(privateKey), 'password');

    const savingFirstData = await SInfo.setItem(key, encryptedValue, {
      sharedPreferencesName: prefName,
      keychainService: keychainService,
      showModal: true,
      touchID: true,
      kSecAccessControl: 'kSecAccessControlBiometryAny',
    });

    console.log('Saved Data => ', savingFirstData);
  } catch (error) {
    console.log(error);
    Alert.alert('Error', `Failed to save JWK file.${error} `);
  }
}


export const getStoredKey = async () => {
  const encryptedData = await SInfo.getItem(key, {
    sharedPreferencesName: prefName,
    keychainService: keychainService,
    showModal: true,
    touchID: true,
    kSecAccessControl: 'kSecAccessControlBiometryAny',
  });

  const decreptedValue = decryptJSON(encryptedData, 'password');
  console.log("Result Data==>", decreptedValue + '\n' + encryptedData);
}

import React, {useEffect, useState, useCallback, useRef} from 'react';
import {View, Text, StyleSheet, Alert} from 'react-native';
import qs from 'query-string';

import Button from '../../components/Button';
import SigningKeyWarning from '../../components/SigningKeyWarning';
import BottomSheetModal from '../../components/BottomSheetModal';

import {colors} from '../../config/constants';
import {useDispatch, useSelector} from 'react-redux';
import CenteredModal from '../../components/CenteredModal';
import PassphraseModal from '../Setting/GenerateKey/PassphraseModal';
import ExportModal from '../Setting/GenerateKey/ExportModal';
import {setPrivateKey, setPublicKey} from '../../redux/profileSlice';

import DocumentPicker from 'react-native-document-picker';
import {decryptJSON} from '../../utils/file-manager';
import {
  isKeyStored,
  storePrivateKey,
  storePublicKey,
} from '../../utils/keychain-store';

import {updatePublicKey} from '../../services/profile';
import useSocket from '../../hooks/useSocket';
import useMessageText from '../../hooks/useMessageText';
import {getLanguageText} from '../../utils/language';

import {promptBiometrics} from '../../services/biometrics';

const ImportKey = props => {
  const dispatch = useDispatch();
  
  // Use ref to track deep link processing state
  const isProcessingDeepLink = useRef(false);
  
  // Main UI state
  const [uiState, setUiState] = useState({
    showWarning: false,
    showPassphraseModal: false,
    isProcessing: false,
    content: null
  });
  
  // Keep key data separate
  const [keyData, setKeyData] = useState({
    newPrivateKey: null,
    newPublicKey: null
  });
  
  // Redux selectors
  const {privateKey} = useSelector(state => state.profile);
  const {user} = useSelector(state => state.currentUser);
  const {wm} = useSocket();
  const {messageText} = useMessageText();
  const charkText = messageText?.chark?.msg;
  const user_ent = user?.curr_eid;
  
  // Process key data once available
  useEffect(() => {
    if (keyData.newPublicKey && keyData.newPrivateKey) {
      console.log("Both keys available, storing keys");
      storeKeys();
    }
  }, [keyData.newPublicKey, keyData.newPrivateKey]);
  
  // Handle deep link processing from props
  useEffect(() => {
    const processDeepLink = () => {
      // Don't process if we're already handling a deep link
      if (isProcessingDeepLink.current) {
        console.log("Already processing a deep link, skipping");
        return;
      }
      
      // Check for signkey URL in props or route params
      const signkeyUrl = props.signkeyUrl || props.route?.params?.signkeyUrl;
      const autoImport = props.autoImport || props.route?.params?.autoImport;
      const jsonData = props.jsonData || props.route?.params?.jsonData;
      
      // Handle signkey URL
      if (signkeyUrl) {
        
        // Set processing flag
        isProcessingDeepLink.current = true;
        
        try {
          const jsonFormat = extractKeyDataFromUrl(signkeyUrl);
          
          if (jsonFormat && autoImport) {
            // Store content for decryption
            setUiState(prev => ({
              ...prev,
              content: jsonFormat
            }));
            
            // Show appropriate UI based on existing key
            if (privateKey) {
              setUiState(prev => ({...prev, showWarning: true}));
            } else {
              setUiState(prev => ({...prev, showPassphraseModal: true}));
            }
          }
        } catch (error) {
          console.error("Error processing URL:", error);
          Alert.alert('Error', 'Invalid signing key format');
          isProcessingDeepLink.current = false;
        }
      }
      
      // Handle direct JSON data
      else if (jsonData && autoImport) {
        // Set processing flag
        isProcessingDeepLink.current = true;
        
        // Store content
        setUiState(prev => ({
          ...prev,
          content: JSON.stringify(jsonData)
        }));
        
        // Show appropriate UI
        if (privateKey) {
          setUiState(prev => ({...prev, showWarning: true}));
        } else {
          setUiState(prev => ({...prev, showPassphraseModal: true}));
        }
      }
    };
    
    // Process deep links when props change
    processDeepLink();
    
    // Cleanup when dependencies change
    return () => {
      isProcessingDeepLink.current = false;
    };
  }, [props.signkeyUrl, props.route?.params?.signkeyUrl, props.jsonData, props.route?.params?.jsonData]); // Run when deep link URLs change

  // Extract key data from URL
  const extractKeyDataFromUrl = (url) => {
    try {
      // Parse the URL to extract parameters
      const parsed = qs.parseUrl(url);
      const params = parsed.query;
      
      console.log("Parsed parameters:", JSON.stringify(params));
      
      // Validate required parameters
      if (!params.s || !params.i || !params.d) {
        console.error("Missing required parameters in signkey URL");
        Alert.alert('Error', 'Invalid signing key link format');
        return null;
      }
      
      // Create the signkey JSON format expected by decryptJSON
      const signkeyData = JSON.stringify({
        signkey: {
          s: params.s,
          i: params.i,
          d: params.d
        }
      });
      
      console.log("Created signkey data for import");
      return signkeyData;
    } catch (error) {
      console.error('Error processing URL:', error);
      throw error;
    }
  };

  // Handle file import
  const importFromFile = async () => {
    try {
      // Reset state to ensure we're starting fresh
      setUiState(prev => ({
        ...prev,
        content: null,
        isProcessing: true,
        showWarning: false,
        showPassphraseModal: false
      }));
      
      // Get biometric confirmation
      await promptBiometrics('Confirm biometrics to import key');
      
      // Open file picker
      const results = await DocumentPicker.pick({
        type: [DocumentPicker.types.allFiles],
        mode: 'open',
        requestLongTermAccess: false,
      });
      
      const result = results[0];
      if (result?.uri) {
        await readFileContent(result.uri);
      } else {
        throw new Error('No file selected');
      }
    } catch (err) {
      // Handle cancellation
      if (DocumentPicker.isCancel(err)) {
        console.log('User cancelled file picker');
      } else {
        console.error('Error during file import:', err);
        Alert.alert('Error', err.toString());
      }
      
      // Reset processing state
      setUiState(prev => ({...prev, isProcessing: false}));
    }
  };

  // Read file content
  const readFileContent = async (fileUri) => {
    try {
      // Import ReactNativeFS
      const ReactNativeFS = require('react-native-fs');
      
      // Read and parse file
      const fileContent = await ReactNativeFS.readFile(fileUri, 'utf8');
      const jsonData = JSON.parse(fileContent);
      
      // Update state with file content and show passphrase modal
      setUiState(prev => ({
        ...prev,
        content: JSON.stringify(jsonData),
        showPassphraseModal: true,
        isProcessing: false
      }));
    } catch (err) {
      console.error('Error reading file:', err);
      Alert.alert('Error', getLanguageText(charkText, 'fail', 'title'));
      setUiState(prev => ({...prev, isProcessing: false}));
    }
  };

  // Decrypt key using passphrase
  const decryptKey = (passphrase) => {
    // Update UI state
    setUiState(prev => ({
      ...prev,
      showPassphraseModal: false,
      isProcessing: true
    }));
    
    // Decrypt the content
    decryptJSON(uiState.content, passphrase)
      .then(data => {
        // Extract private key
        const privateKey = data;
        
        // Derive public key by removing private component
        const publicKey = JSON.parse(data);
        delete publicKey.d;
        publicKey.key_ops = ['verify'];
        
        // Set both keys to trigger storage
        setKeyData({
          newPrivateKey: privateKey,
          newPublicKey: JSON.stringify(publicKey)
        });
      })
      .catch(e => {
        console.error('Decrypt Error:', e);
        Alert.alert('Error', e.toString());
        
        // Reset UI state on error
        setUiState(prev => ({
          ...prev, 
          isProcessing: false
        }));
        
        // Allow future deep link processing
        isProcessingDeepLink.current = false;
      });
  };

  // Store keys in backend and secure storage
  const storeKeys = async () => {
    try {
      // 1. Update backend with public key
      await updatePublicKey(wm, {
        public_key: JSON.parse(keyData.newPublicKey),
        where: {
          user_ent,
        },
      });
      
      // 2. Store locally in secure storage
      await Promise.all([
        storePublicKey(keyData.newPublicKey),
        storePrivateKey(keyData.newPrivateKey),
      ]);
      
      // 3. Update Redux store
      dispatch(setPublicKey(keyData.newPublicKey));
      dispatch(setPrivateKey(keyData.newPrivateKey));
      
      // 4. Show success
      Alert.alert('Success', getLanguageText(charkText, 'success'));
      
      // 5. Reset all state
      setUiState({
        showWarning: false,
        showPassphraseModal: false,
        isProcessing: false,
        content: null
      });
      
      setKeyData({
        newPrivateKey: null,
        newPublicKey: null
      });
      
      // Allow new deep link processing
      isProcessingDeepLink.current = false;
    } catch (ex) {
      console.error('Error storing keys:', ex);
      Alert.alert('Error', getLanguageText(charkText, 'fail'));
      
      setUiState(prev => ({
        ...prev, 
        isProcessing: false
      }));
      
      // Allow new deep link processing
      isProcessingDeepLink.current = false;
    }
  };

  // Import button click handler
  const onImportClick = () => {
    // Cancel any ongoing deep link processing to allow file import
    isProcessingDeepLink.current = false;
    
    // Reset content to ensure fresh file import
    setUiState(prev => ({
      ...prev,
      content: null
    }));
    
    // Show warning if key exists, otherwise proceed directly
    if (privateKey) {
      setUiState(prev => ({...prev, showWarning: true}));
    } else {
      importFromFile();
    }
  };

  // Warning dialog cancel
  const onWarningCancel = () => {
    setUiState(prev => ({...prev, showWarning: false}));
    isProcessingDeepLink.current = false;
  };

  // Warning dialog accept
  const onWarningAccept = () => {
    setUiState(prev => ({...prev, showWarning: false}));
    
    // If we have content, decrypt it, otherwise do file import
    if (uiState.content) {
      setUiState(prev => ({...prev, showPassphraseModal: true}));
    } else {
      importFromFile();
    }
  };

  // Cancel passphrase modal
  const onPassphraseCancel = () => {
    setUiState(prev => ({...prev, showPassphraseModal: false}));
    isProcessingDeepLink.current = false;
  };

  return (
    <>
      <View style={{marginTop: 30}}>
        <Text style={styles.importText}>{props?.text?.import?.title ?? 'chark:import:title'}</Text>
        <Text style={styles.importDescription}>
          {props?.text?.import?.help ?? 'chark:import:help'}
        </Text>

        <Button
          style={styles.importBtn}
          title={props?.text?.import?.title ?? 'chark:import:title'}
          onPress={onImportClick}
          disabled={uiState.isProcessing}
        />
        {uiState.isProcessing && (
          <Text style={styles.processingText}>Processing...</Text>
        )}
      </View>

      <BottomSheetModal 
        isVisible={uiState.showWarning} 
        onClose={onWarningCancel}
      >
        <SigningKeyWarning
          loading={false}
          title={props?.text?.keywarn?.title ?? 'chark:keywarn:title'}
          description={props?.text?.keywarn?.help ?? 'chark:keywarn:help'}
          onAccept={onWarningAccept}
          onCancel={onWarningCancel}
        />
      </BottomSheetModal>

      <CenteredModal
        isVisible={uiState.showPassphraseModal}
        onClose={onPassphraseCancel}
      >
        <PassphraseModal
          action="import_without"
          onPassphraseConfirmed={decryptKey}
          cancel={onPassphraseCancel}
          buttonTitle={getLanguageText(charkText, 'import')}
        />
      </CenteredModal>
    </>
  );
};

const styles = StyleSheet.create({
  importText: {
    color: colors.black,
    fontSize: 15,
    fontFamily: 'inter',
    fontWeight: '500',
  },
  importDescription: {
    color: colors.gray300,
    fontWeight: '500',
    fontFamily: 'inter',
    fontSize: 12,
    lineHeight: 13,
  },
  importBtn: {
    marginTop: 16,
    width: '50%',
    height: 30,
  },
  processingText: {
    marginTop: 8,
    color: colors.primary,
    fontSize: 12,
    fontFamily: 'inter',
  },
});

export default ImportKey;
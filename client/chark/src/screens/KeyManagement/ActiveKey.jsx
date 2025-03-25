import React, { useEffect, useState } from 'react';
import { useSelector, useDispatch } from 'react-redux';
import { View, Text, StyleSheet, TouchableOpacity } from 'react-native';
import PropTypes from 'prop-types';

import EyeIcon from '../../../assets/svg/eye_icon.svg';
import { colors, keyServices } from '../../config/constants';
import { retrieveKey } from '../../utils/keychain-store';
import { setPrivateKey, setPublicKey } from '../../redux/profileSlice';

const ActiveKey = (props) => {
  const dispatch = useDispatch();
  const { publicKey, privateKey } = useSelector(state => state.profile);
  const [showPrivateKey, setShowPrivateKey] = useState(false);

  useEffect(() => {
    const loadKeysFromStorage = async () => {
      try {
        console.log("DEBUG ActiveKey: Loading keys from storage, current publicKey exists:", !!publicKey);
        
        // Load both keys in parallel for better performance
        const [publicKeyResult, privateKeyResult] = await Promise.all([
          retrieveKey(keyServices.publicKey),
          retrieveKey(keyServices.privateKey)
        ]);
        
        console.log("DEBUG ActiveKey: Retrieved publicKey from storage:", !!publicKeyResult?.password);
        console.log("DEBUG ActiveKey: Retrieved privateKey from storage:", !!privateKeyResult?.password);
        
        // Only update Redux if we successfully retrieved keys
        if (publicKeyResult?.password && !publicKey) {
          console.log("DEBUG ActiveKey: Dispatching setPublicKey");
          dispatch(setPublicKey(publicKeyResult.password));
        }
        
        if (privateKeyResult?.password && !privateKey) {
          console.log("DEBUG ActiveKey: Dispatching setPrivateKey");
          dispatch(setPrivateKey(privateKeyResult.password));
        }
      } catch (err) {
        console.error("Error retrieving keys:", err);
      }
    };
    
    loadKeysFromStorage();
    console.log("DEBUG ActiveKey: useEffect dependencies:", {publicKey: !!publicKey, privateKey: !!privateKey});
  }, [publicKey, privateKey])
  
  const togglePrivateKeyVisibility = () => {
    setShowPrivateKey(!showPrivateKey);
  }

  return (
    <>
      <View>
        <Text style={styles.headerText}>
          {props?.text?.public?.title ?? ''}
        </Text>

        <View style={styles.keySection}>
          {publicKey ? (
            <Text style={styles.key}>
              {publicKey}
            </Text>
          ) : (
            <Text style={styles.keyMissing}>
              {props?.text?.nokey?.title ?? 'chark:nokey:title'}
            </Text>
          )}
        </View>
      </View>

      <View style={{ marginTop: 30 }}>
        <View style={styles.headerRow}>
          <Text style={styles.headerText}>
            {props?.text?.private?.title ?? ''}
          </Text>
          {privateKey && (
            <TouchableOpacity onPress={togglePrivateKeyVisibility}>
              <EyeIcon width={18} height={18} />
            </TouchableOpacity>
          )}
        </View>

        {showPrivateKey && privateKey ? (
          <View style={styles.keySection}>
            <Text style={styles.key}>
              {privateKey}
            </Text>
          </View>
        ) : (
          privateKey ? null : (
            <View style={styles.keySection}>
              <Text style={styles.keyMissing}>
                {props?.text?.nokey?.title ?? 'chark:nokey:title'}
              </Text>
            </View>
          )
        )}
      </View>
    </>
  )
}

const styles = StyleSheet.create({
  headerRow: {
    flexDirection: 'row',
    alignItems: 'center',
    marginBottom: 8,
  },
  headerText: {
    fontFamily: 'inter',
    fontWeight: '500',
    fontSize: 12,
    color: colors.gray300,
    marginRight: 8,
  },
  keySection: {
    borderColor: colors.gray,
    borderWidth: 1,
    paddingVertical: 7,
    paddingHorizontal: 10,
    borderRadius: 5,
  },
  key: {
    color: colors.black,
    fontSize: 12,
    lineHeight: 14,
  },
  keyMissing: {
    color: colors.gray300,
    fontSize: 12,
    lineHeight: 14,
    fontStyle: 'italic',
  }
});

ActiveKey.propTypes = {
  text: PropTypes.object,
}

export default ActiveKey;

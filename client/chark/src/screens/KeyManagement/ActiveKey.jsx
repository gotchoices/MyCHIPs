import React, { useEffect, useState } from 'react';
import { useSelector, useDispatch } from 'react-redux';
import { View, Text, StyleSheet } from 'react-native';

import { colors, keyServices } from '../../config/constants';
import { retrieveKey } from '../../utils/keychain-store';
import { setPrivateKey, setPublicKey } from '../../redux/profileSlice';

const ActiveKey = () => {
  const dispatch = useDispatch();
  const { publicKey, privateKey } = useSelector(state => state.profile);

  useEffect(() => {
    retrieveKey(keyServices.publicKey).then((key) => {
      dispatch(setPublicKey(key.password))
    })

    retrieveKey(keyServices.privateKey).then((key) => {
      dispatch(setPrivateKey(key.password))
    })
  }, [setPrivateKey, setPublicKey])

  return (
    <>
      <View>
        <Text style={styles.headerText}>
          Active public key
        </Text>

        <View style={styles.keySection}>
          <Text style={styles.key}>
            {publicKey}
          </Text>
        </View>
      </View>

      <View style={{ marginTop: 30 }}>
        <Text style={styles.headerText}>
          Active private key
        </Text>

        <View style={styles.keySection}>
          <Text style={styles.key}>
            {privateKey}
          </Text>
        </View>
      </View>
    </>
  )
}

const styles = StyleSheet.create({
  headerText: {
    fontFamily: 'inter',
    fontWeight: '500',
    fontSize: 12,
    color: colors.gray300,
    marginBottom: 8,
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
  }
});

export default ActiveKey;

import React from 'react';
import { View, Text, StyleSheet } from 'react-native';

import { colors } from '../../config/constants';

const NoActivity = () => {
  return (
    <View style={styles.container}>
      <Text style={styles.title}>
        No Activity
      </Text>

      <Text style={styles.description}>
        MyChips activity will show here i.e. tally requests, payment requests, transaction history
      </Text>
    </View>
  )
}

const styles = StyleSheet.create({
  title: {
    color: colors.gray10,
    fontFamily: 'inter',
    fontSize: 24,
    fontWeight: '500',
    textAlign: 'center',
    marginBottom: 4,
  },
  description: {
    color: colors.gray10,
    fontFamily: 'inter',
    fontSize: 16,
    fontWeight: '500',
    textAlign: 'center',
  }
});

export default NoActivity;

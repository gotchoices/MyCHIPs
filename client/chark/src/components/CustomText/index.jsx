import React from 'react';
import { Text, StyleSheet } from 'react-native';

import { colors } from '../../config/constants'

const CustomText = (props) => {
  const { style = {}, children, as = 'p' } = props;

  return (
    <Text style={[styles.base, styles[as], style]}>
      {children}
    </Text>
  )
}

const styles = StyleSheet.create({
  base: {
    color: colors.black,
    marginBottom: 5,
  },
  h1: {
    fontSize: 30,
    lineHeight: 41,
    fontWeight: 'bold',
  },
  h2: {
    fontSize: 24,
    lineHeight: 33,
    fontWeight: 'bold',
  },
  h3: {
    fontSize: 16,
    lineHeight: 20,
    fontWeight: 'bold',
  },
  h4: {
    fontSize: 14,
    lineHeight: 19,
    fontWeight: 'bold',
  },
  h5: {
    fontSize: 12,
    lineHeight: 16,
    fontWeight: 'bold',
  },
  p: {}
});

export default CustomText;

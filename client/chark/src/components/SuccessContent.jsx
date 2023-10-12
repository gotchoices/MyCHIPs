import React from 'react';
import { View, Text, StyleSheet } from 'react-native';
import PropTypes from 'prop-types';

import Button from './Button';
import CustomIcon from './CustomIcon';

import { colors } from '../config/constants';

const SuccessContent = (props) => {
  return (<View style={styles.bottomSheetContainer}>
    <CustomIcon
      name="close"
      size={16}
      onPress={props.onDismiss}
      style={styles.close}
    />
    <Text style={styles.bottomSheetTitle}>🎉Success🎉</Text>
    <Text style={styles.bottomSheetSub}>{props.message}</Text>

    <View style={{ flex: 1 }} />

    <Button
      title={props.buttonTitle ?? 'Done'}
      onPress={props.onDone}
      style={styles.button}
    />
  </View>);
}

SuccessContent.propTypes = {
  buttonTitle: PropTypes.string,
  onDone: PropTypes.func.isRequired,
  onDismiss: PropTypes.func.isRequired,
  message: PropTypes.string.isRequired,
}

const styles = StyleSheet.create({
  bottomSheetContainer: {
    height: 316,
    paddingHorizontal: 16,
    paddingVertical: 24,
    alignItems: 'center',
  },
  bottomSheetTitle: {
    fontSize: 32,
    fontWeight: '500',
    fontFamily: 'inter',
    color: colors.black,
  },
  bottomSheetSub: {
    fontSize: 18,
    fontWeight: '500',
    color: '#636363',
    fontFamily: 'inter',
    marginTop: 16,
  },
  button: {
    backgroundColor: colors.blue2,
    borderColor: colors.blue2,
    width: '100%',
    borderRadius: 40,
    height: 45,
    alignItems: 'center',
    justifyContent: 'center',
  },
  close: {
    alignSelf: 'flex-end',
    backgroundColor: 'white',
    height: 24,
    width: 24,
    justifyContent: 'center',
    alignItems: 'center',
  }
});

export default SuccessContent;

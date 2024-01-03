import React from 'react'
import { View, Text, StyleSheet } from 'react-native';
import PropTypes from 'prop-types';

import Button from './Button';
import WarningIcon from '../../assets/svg/ic_warning.svg';

import { colors } from '../config/constants';

const SigningKeyWarning = (props) => {
  return (
    <View style={styles.container}>
      <View style={styles.header}>
        <WarningIcon />
        
        <Text style={styles.warning}>Warning</Text>

        <Text style={styles.title}>{props.title}</Text>
      </View>

      <Text style={styles.description}>{props.description}</Text>
      
      <View style={styles.action}>
        <Button
          title="I understand"
          textColor={colors.blue}
          style={styles.acceptBtn}
          onPress={props.onAccept}
        />

        <Button
          title="Cancel"
          disabled={props.loading}
          style={styles.cancelBtn}
          onPress={props.onCancel}
        />
      </View>
    </View>
  )
}

const font = {
  FontFamily: 'inter',
  fontWeight: '500',
};

const styles = StyleSheet.create({
  container: {
    paddingVertical: 30,
    paddingHorizontal: 20,
  },
  header: {
    alignItems: 'center'
  },
  warning: {
    ...font,
    fontSize: 30,
    color: colors.yellow,
    marginBottom: 12,
  },
  title: {
    ...font,
    width: 200,
    fontSize: 16,
    textAlign: 'center',
    color: colors.black,
    marginBottom: 20,
  },
  description: {
    ...font,
    fontSize: 12,
  },
  action: {
    marginTop: 45,
    marginBottom: 12,
    flexDirection: 'row',
    justifyContent: 'center'
  },
  acceptBtn: {
    marginRight: 20,
    minWidth: 132,
    backgroundColor: colors.white,
  },
  cancelBtn: {
    marginLeft: 20,
    paddingHorizontal: 25,
    minWidth: 132,
  },
});

SigningKeyWarning.propTypes = {
  title: PropTypes.string.isRequired,
  description: PropTypes.string.isRequired,
  onAccept: PropTypes.func.isRequired,
  onCancel: PropTypes.func.isRequired,
  loading: PropTypes.bool.isRequired,
}

export default SigningKeyWarning;

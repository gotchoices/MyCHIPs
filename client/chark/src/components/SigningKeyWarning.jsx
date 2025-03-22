import React from 'react'
import { View, Text, StyleSheet } from 'react-native';
import PropTypes from 'prop-types';

import Button from './Button';
import WarningIcon from '../../assets/svg/warning_icon.svg';

import { colors } from '../config/constants';
import useMessageText from '../hooks/useMessageText';

const SigningKeyWarning = (props) => {
  const { messageText } = useMessageText();

  const charkText = messageText?.chark?.msg;

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
          title={charkText?.cancel?.title ?? ''}
          disabled={props.loading}
          style={styles.primaryBtn}
          onPress={props.onCancel}
        />

        <Button
          title={charkText?.proceed?.title ?? ''}
          style={styles.secondaryBtn}
          textColor={colors.blue}
          onPress={props.onAccept}
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
  primaryBtn: {
    marginRight: 20,
    minWidth: 132,
    backgroundColor: colors.blue,
  },
  secondaryBtn: {
    marginLeft: 20,
    paddingHorizontal: 25,
    minWidth: 132,
    backgroundColor: colors.white,
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

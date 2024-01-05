import React from 'react';
import {
  Text,
  View,
  StyleSheet,
  TouchableWithoutFeedback,
} from 'react-native'
import PropTypes from 'prop-types';

import { colors } from '../../config/constants';

const Button = (props) => {
  return (
    <TouchableWithoutFeedback
      onPress={props.onPress}
      disabled={props.disabled ?? false}
      testID={props.testID ?? ''}
    >
      <View
        style={[styles.btn, props.style ?? {}, props.disabled ? styles.btnDisabled : {}]}
      >
        <Text
          style={[styles.title, props.textStyle ?? {}, { color: props.textColor ?? colors.white,}, props.disabled ? styles.titleDisabled : {}]}
        >
          {props.title}
        </Text>
      </View>
    </TouchableWithoutFeedback>
  );
}

Button.propTypes = {
  title: PropTypes.string.isRequired,
  textColor: PropTypes.string,
  onPress: PropTypes.func.isRequired,
  testID: PropTypes.string,
  style: PropTypes.oneOfType([
    PropTypes.object,
    PropTypes.arrayOf(PropTypes.object)
  ]),
  textStyle: PropTypes.oneOfType([
    PropTypes.object,
    PropTypes.arrayOf(PropTypes.object)
  ]),
}

const styles = StyleSheet.create({
  btn: {
    borderRadius: 40,
    borderWidth: 1,
    borderColor: colors.blue,
    alignItems: 'center',
    justifyContent:"center",
    paddingHorizontal: 6,
    height: 45,
    backgroundColor: colors.blue,
    shadowColor: colors.black,
    shadowOpacity: 0.5,
    shadowRadius: 2,
    shadowOffset: {
      height: 1,
      width: 1
    }
  },
  btnDisabled: {
    backgroundColor: colors.lightgray,
    borderColor: colors.lightgray,
  },
  title: {
    fontSize: 12,
    fontWeight: '500',
  },
  titleDisabled: {
    color: colors.gray700,
  }
});

export default Button;

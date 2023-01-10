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
    >
      <View style={[styles.btn, props.style ?? {}]}>
        <Text style={[styles.title, { color: props.textColor ?? colors.white }]}>
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
}

const styles = StyleSheet.create({
  btn: {
    paddingHorizontal: 6,
    paddingVertical: 8,
    backgroundColor: colors.blue,
    shadowColor: colors.black,
    shadowOpacity: 0.5,
    shadowRadius: 2,
    shadowOffset: {
      height: 1,
      width: 1
    }
  },
  title: {
    textTransform: 'uppercase',
    fontSize: 12,
  },
});

export default Button;

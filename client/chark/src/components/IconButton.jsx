import React from 'react';
import {
  View,
  TouchableWithoutFeedback,
} from 'react-native'
import PropTypes from 'prop-types';

const IconButton = (props) => {
  return (
    <TouchableWithoutFeedback
      onPress={props.onPress}
      disabled={props.disabled ?? false}
      testID={props.testID ?? ''}
    >
      <View
        style={[props.style ?? {}, /*props.disabled ? styles.btnDisabled : {}*/]}
      >
        {props.children}
      </View>
    </TouchableWithoutFeedback>
  );
}

IconButton.propTypes = {
  onPress: PropTypes.func.isRequired,
  testID: PropTypes.string,
  style: PropTypes.object,
}

export default IconButton;

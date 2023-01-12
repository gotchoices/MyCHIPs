import React, { useState } from 'react';
import {
  View,
  StyleSheet,
  TextInput,
  Text,
  TouchableWithoutFeedback
} from 'react-native';
import Icon from 'react-native-vector-icons/FontAwesome';
import Tooltip from 'react-native-walkthrough-tooltip';
import PropTypes from 'prop-types';

import { colors } from '../../config/constants';

const HelpTextInput = (props) => {
  const [isVisible, setIsVisible] = useState(false);

  return (
    <View style={styles.formControl}>
      <View style={styles.labelWrapper}>
        <Text style={styles.label}>
          {props.label} 
        </Text>

        {
          props.helpText && (
            <Tooltip
              isVisible={isVisible}
              content={
                <Text>{props.helpText}</Text>
              }
              placement="right"
              onClose={() => setIsVisible(false)}
            >
              <TouchableWithoutFeedback 
                onPress={() => setIsVisible(true)}
              >
                <Icon
                  name="question-circle"
                  size={12}
                  color={colors.blue}
                  style={{ marginLeft: 5 }}
                />
              </TouchableWithoutFeedback>
            </Tooltip>
          )
        }

      </View>

      <TextInput 
        style={[styles.input, props?.inputStyle ?? {}]}
        value={props.value}
        onChangeText={props.onChange}
      />
    </View>
  )
}

const styles = StyleSheet.create({
  formControl: {
    marginVertical: 10,
  },
  labelWrapper: {
    flexDirection: 'row',
    alignItems: 'center',
    marginBottom: 8,
  },
  label: {
    fontSize: 12,
    fontWeight: '400',
  },
  input: {
    padding: 10,
    backgroundColor: colors.gray100,
  },
});

HelpTextInput.propTypes = {
  label: PropTypes.string.isRequired,
  helpText: PropTypes.string,
  value: PropTypes.string.isRequired,
  value: PropTypes.oneOfType([
    PropTypes.string,
    PropTypes.number,
  ]),
  onChange: PropTypes.func.isRequired,
  inputStyle: PropTypes.object, 
}

export default HelpTextInput;


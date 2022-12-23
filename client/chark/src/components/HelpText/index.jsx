import React, { useState } from 'react';
import {
  View,
  StyleSheet,
  Text,
  TouchableWithoutFeedback
} from 'react-native';
import Icon from 'react-native-vector-icons/FontAwesome';
import Tooltip from 'react-native-walkthrough-tooltip';
import PropTypes from 'prop-types';

import { colors } from '../../config/constants';

const HelpText = (props) => {
  const [isVisible, setIsVisible] = useState(false);

  return (
      <View style={styles.labelWrapper}>
        <Text style={[styles.label, props?.style ?? {}]}>
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
                  size={13}
                  color={colors.blue}
                  style={{ marginLeft: 5 }}
                />
              </TouchableWithoutFeedback>
            </Tooltip>
          )
        }
      </View>
  )
}

const styles = StyleSheet.create({
  labelWrapper: {
    flexDirection: 'row',
    alignItems: 'center',
    marginBottom: 8,
  },
  label: {
    fontWeight: 'bold',
  },
});

HelpText.propTypes = {
  label: PropTypes.string.isRequired,
  helpText: PropTypes.string,
  style: PropTypes.object,
}

export default HelpText;


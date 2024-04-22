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

import { colors } from '../config/constants';

const IconTooltip = (props) => {
  const [isVisible, setIsVisible] = useState(false);

  return (
      <View style={styles.labelWrapper}>
        <Tooltip
          isVisible={isVisible}
          content={
            <Text>{props.text}</Text>
          }
          placement={props.placement ?? 'top'}
          onClose={() => setIsVisible(false)}
        >
          <TouchableWithoutFeedback 
            onPress={() => setIsVisible(true)}
          >
            <View style={{ paddingRight: 6, paddingVertical: 4 }}>
              <Icon
                name="question-circle"
                size={15}
                color={colors.blue}
                style={{ marginLeft: 5 }}
              />
            </View>
          </TouchableWithoutFeedback>
        </Tooltip>
      </View>
  )
}

const styles = StyleSheet.create({
  labelWrapper: {
    marginBottom: 5,
    alignItems: 'center',
    flexDirection: 'row',
  },
  label: {
    fontSize: 12,
    fontWeight: '500',
    fontFamily: 'inter',
  },
});

IconTooltip.propTypes = {
  text: PropTypes.string,
  style: PropTypes.oneOfType([
    PropTypes.object,
    PropTypes.arrayOf(PropTypes.object)
  ]),

}

export default IconTooltip;


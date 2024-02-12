import React from 'react';
import {
  View,
  Text,
  StyleSheet,
} from 'react-native';
import PropTypes from 'prop-types';

import HelpText from '../../../components/HelpText';

import { colors } from '../../../config/constants';
import useMessageText from '../../../hooks/useMessageText';

const ChitTypeText = (props) => {
  const { messageText } = useMessageText()

  const chits_msg = messageText?.chits_v_me?.msg;

  return (
    <View>
      {props.state === 'L.pend' && (
        <HelpText
          label={chits_msg?.liability?.title ?? ''}
          helpText={chits_msg?.liability?.help}
        />
      )}

      {props.state === 'A.pend' && (
        <HelpText
          label={chits_msg?.asset?.title ?? ''}
          helpText={chits_msg?.asset?.help}
        />
      )}

      {props.state === 'A.good' && (
        <View style={{ flexDirection: 'row' }}>
          <Text style={styles.name}>
            {props.name}
          </Text>
          <Text style={styles.text}> paid you for</Text>
        </View>
      )}

      {props.state === 'L.good' && (
        <View style={{ flexDirection: 'row' }}>
          <Text style={styles.text}>You paid </Text>
          <Text style={styles.name}>
            {props.name}
          </Text>
          <Text style={styles.text}> for</Text>
        </View>
      )}

    </View>
  )
}

const styles = StyleSheet.create({
  text: {
    fontFamily: 'inter',
    color: colors.black,
  },
  name: {
    fontFamily: 'inter',
    color: colors.black,
    fontWeight: '700',
    textDecorationLine: 'underline',
  },
});

ChitTypeText.propTypes = {
  name: PropTypes.string.isRequired,
  state: PropTypes.string.isRequired,
}


export default ChitTypeText;

import React from 'react';
import { View, Text, StyleSheet } from 'react-native';

import HelpText from '../../../components/HelpText';

import { colors } from '../../../config/constants';
import useMessageText from '../../../hooks/useMessageText';

const CommonTallyView = (props) => {
  const tally = props.tally;
  const { messageText } = useMessageText();

  return (
    <View>
      <View style={styles.detailControl}>
        <HelpText
          label={messageText?.tally_uuid?.title ?? ''}
          helpText={messageText?.tally_uuid?.help}
          style={styles.headerText}
        />
        <Text>
          {tally.tally_uuid}
        </Text>
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={messageText?.tally_date?.title ?? ''}
          helpText={messageText?.tally_date?.help}
          style={styles.headerText}
        />
        <Text>
          {new Date(tally.tally_date).toLocaleString()}
        </Text>
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={messageText?.status?.title ?? ''}
          helpText={messageText?.status?.help}
          style={styles.headerText}
        />

        <Text>
          {tally.status}
        </Text>
      </View>
    </View>
  )
}

const styles = StyleSheet.create({
  detailControl: {
    marginVertical: 10
  },
  headerText: {
    color: colors.black,
    fontSize: 14,
  },
})

export default CommonTallyView;

import React from 'react';
import { View, Text, StyleSheet } from 'react-native';

import CustomText from '../../../components/CustomText';

const CommonTallyView = (props) => {
  const tally = props.tally;

  return (
    <View>
      <View style={styles.detailControl}>
        <CustomText as="h4">
          UUID
        </CustomText>

        <Text>
          {tally.tally_uuid}
        </Text>
      </View>

      <View style={styles.detailControl}>
        <CustomText as="h4">
          Tally Date
        </CustomText>

        <Text>
          {new Date(tally.tally_date).toLocaleString()}
        </Text>
      </View>

      <View style={styles.detailControl}>
        <CustomText as="h4">
          Status
        </CustomText>

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
})

export default CommonTallyView;

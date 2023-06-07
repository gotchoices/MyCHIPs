import React from 'react';
import { View, Text, StyleSheet, TouchableOpacity } from 'react-native';

import { colors } from '../../../config/constants';

const TemplateItem = (props) => {
  const item = props.template;

  const onView = () => {
    props.navigation.navigate('TallyPreview', {
      tally_seq: item.id,
      tally_ent: item.tally_ent,
    });
  }

  return (
    <View style={styles.container} testID={props.testID}>
      <TouchableOpacity onPress={onView}>
        <View style={styles.item}>
          <Text style={styles.comment}>{item.comment}</Text>
          <Text>Tally type: {item.tally_type ?? 'N/A'}</Text>
          <Text>Partner CID: {item.part_cid ?? 'N/A'}</Text>
          <Text>Status: {item.status ?? 'N/A'}</Text>
          <Text>Holder Credit limit: {item?.hold_terms?.limit ?? 'N/A'}</Text>
          <Text>Partner Credit limit: {item?.part_terms?.limit ?? 'N/A'}</Text>
        </View>
      </TouchableOpacity>
    </View>
  )
}

const itemStyle = {
  borderWidth: 1,
  borderColor: '#DDD',
  borderRadius: 5,
  padding: 10,
  marginBottom: 1,
}

const styles = StyleSheet.create({
  container: {
    marginBottom: 5,
  },
  item: itemStyle,
  comment: {
    fontWeight: 'bold',
    color: colors.black,
    marginBottom: 5,
  }
})

export default TemplateItem;

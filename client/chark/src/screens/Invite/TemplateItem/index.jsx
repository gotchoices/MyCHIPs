import React from 'react';
import { View, Text, StyleSheet, TouchableOpacity } from 'react-native';

import Button from '../../../components/Button';

const TemplateItem = (props) => {
  const item = props.template;

  const onPress = () => {
    props.selectTemplate(item.id)
  }

  const onView = () => {
    props.navigation.navigate('TallyEdit', {
      tally_seq: item.id,
      tally_ent: item.tally_ent,
    });
  }

  const isActive = props.activeId === item.id

  return (
    <View style={styles.container}>
      <TouchableOpacity onPress={onPress}>
        <View style={isActive ? styles.activeItem: styles.item}>
          <Text style={isActive && styles.activeText}>{item.comment}</Text>
        </View>
      </TouchableOpacity>

      <Button 
        title="View" 
        onPress={onView}
      />
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
  activeItem: {
    ...itemStyle,
    backgroundColor: '#bdbdbd',
  },
  activeText: {
    color: '#fff',
  }
})

export default TemplateItem;

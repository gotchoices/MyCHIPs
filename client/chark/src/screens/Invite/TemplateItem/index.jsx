import React from 'react';
import { View, Text, StyleSheet, TouchableOpacity } from 'react-native';

const TemplateItem = (props) => {
  const item = props.template;

  const onPress = () => {
    props.selectTemplate(item.id)
  }

  const isActive = props.activeId === item.id

  return (
    <View style={styles.container}>
      <TouchableOpacity onPress={onPress}>
        <View style={isActive ? styles.activeItem: styles.item}>
          <Text style={isActive && styles.activeText}>{item.comment}</Text>
        </View>
      </TouchableOpacity>
    </View>
  )
}

const itemStyle = {
  borderWidth: 1,
  borderColor: '#DDD',
  borderRadius: 5,
  padding: 10 
}

const styles = StyleSheet.create({
  container: {
    marginBottom: 5,
  },
  item: itemStyle,
  activeItem: {
    ...itemStyle,
    backgroundColor: '#2196F3',
  },
  activeText: {
    color: '#fff',
  }
})

export default TemplateItem;

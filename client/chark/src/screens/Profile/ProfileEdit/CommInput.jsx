import React from 'react';
import PropTypes from 'prop-types';
import { View, TextInput, Text, StyleSheet, TouchableWithoutFeedback } from 'react-native';
import Icon from 'react-native-vector-icons/FontAwesome';

import { colors } from '../../../config/constants';

const CommInput = (props) => {
  const item = props.item;

  const onChange = (value) => {
    props.onChange(props.id, value);
  }

  const removeItem = () => {
    props.removeItem(props.index);
  }

  return (
    <View style={styles.inputGroup}>
      <TextInput 
        style={[styles.input, item.comm_prim ? styles.primaryInput : {}]}
        value={item.comm_spec}
        onChangeText={onChange}
      />

    <View
      style={
        [styles.inputRight, item?.comm_prim ? styles.primary : styles.removeIcon]
      }
    >
      {
        item?.comm_prim ? (
          <Text>Primary</Text>
        ) : (
          <TouchableWithoutFeedback onPress={removeItem}>
            <Icon
              size={16}
              name="trash-o"
              color={colors.quicksilver}
            />
          </TouchableWithoutFeedback>
        )
      }
    </View>
  </View>
  )
}

const styles = StyleSheet.create({
  inputGroup: {
    marginBottom: 10,
    height: 50,
    flexDirection: 'row',
  },
  input: {
    paddingLeft: 10,
    backgroundColor: colors.antiflashwhite,
    marginBottom: 8,
    width: '90%',
    height: '100%',
  },
  primaryInput: {
    width: '80%'
  },
  inputRight: {
    backgroundColor: colors.antiflashwhite,
    height: '100%',
    justifyContent: 'center',
  },
  removeIcon: {
    width: '10%'
  },
  primary: {
    color: colors.quicksilver,
    width: '20%',
  },
});

export default CommInput;

import React from "react";
import { View, StyleSheet, TextInput } from "react-native"
import PropTypes from 'prop-types';

const CustomTextInput = (props) => {
  return <View style={[styles.row, props.style]}>
    {props.leadingIcon}
    <TextInput
      value={props.value}
      placeholder={props.placeholder}
      onChangeText={props.onChangeText}
      style={[styles.textInput, props.textInputStyle]}
    />
  </View>
}


CustomTextInput.propTypes = {
  style: PropTypes.object,
  textInputStyle: PropTypes.object,
  placeholder: PropTypes.string,
  value: PropTypes.string,
  onChangeText: PropTypes.func.isRequired,
  leadingIcon: PropTypes.element,
}

const styles = StyleSheet.create({
  row: {
    flexDirection: 'row',
    borderWidth: 1,
    borderColor: '#BBBBBB',
    height: 35,
    paddingHorizontal: 16,
    borderRadius: 8,
    alignItems: 'center',
  },
  textInput: {
    padding: 0,
    marginStart: 12,
    flex: 1,
    fontFamily: 'inter'
  }
});

export default CustomTextInput;
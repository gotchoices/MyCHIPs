// Display status of connection with backend server
// Copyright MyCHIPs.org
// TODO:
//- Make it display connection status
//- Clicking on it will toggle connection status
//- Later: embelish with icons/styles
//- 
import React, { Component } from 'react';
import { View, Text, StyleSheet, Image } from 'react-native';

export default class ServIcon extends Component {
  constructor(props) {
    super(props)
  }

  render() {return (
    <View>
      <Text>Server:{this.props.server}</Text>
    </View>
  )}
}

//const styles = StyleSheet.create({
//  buttonBox: {
//    alignItems: 'center',
//    backgroundColor: '#e0e0e0',
//    borderRadius: 8,
//    flex: 1,
//  },
//})

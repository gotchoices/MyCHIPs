import React, { useState } from "react";
import { View, Text, StyleSheet, TouchableOpacity } from "react-native";
import Button from "../../../components/Button";
import CustomIcon from "../../../components/CustomIcon";
import PropTypes from 'prop-types';
import { colors } from "../../../config/constants";

const SuccessContent = (props) => {

  return (<View style={styles.bottomSheetContainer}>
    <CustomIcon
      name="close"
      size={16}
      onPress={props.onDismiss}
      style={styles.close}
    />
    <Text style={styles.bottomSheetTitle}>🎉Success🎉</Text>
    <Text style={styles.bottomSheetSub}>Your tally has been sent</Text>

    <View style={{ flex: 1 }} />
    <Button
      title='Done'
      onPress={props.onDone}
      style={styles.button}
    />
  </View>);
}


SuccessContent.propTypes = {
  onDone: PropTypes.func.isRequired,
  onDismiss: PropTypes.func.isRequired,
}

const styles = StyleSheet.create({
  bottomSheetContainer: {
    height: 600,
    paddingHorizontal: 16,
    paddingVertical: 24,
    alignItems: 'center',
  },
  bottomSheetTitle: {
    fontSize: 32,
    fontWeight: '500',
    fontFamily: 'inter',
    color: colors.black,
  },
  bottomSheetSub: {
    fontSize: 18,
    fontWeight: '500',
    color: '#636363',
    fontFamily: 'inter',
    marginTop: 16,
  },
  button: {
    backgroundColor: 'blue',
    borderColor: 'blue',
    width: '100%',
    borderRadius: 40,
    height: 45,
    alignItems: 'center',
    justifyContent: 'center',
  },
  close: {
    alignSelf: 'flex-end',
    backgroundColor: 'white',
    height: 24,
    width: 24,
    justifyContent: 'center',
    alignItems: 'center',
  }
});

export default SuccessContent;
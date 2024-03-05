import React, { useState } from "react";
import { View, Text, TextInput, StyleSheet, TouchableOpacity } from "react-native";
import Button from "../../../components/Button";
import CustomIcon from "../../../components/CustomIcon";
import PropTypes from 'prop-types';
import { colors } from "../../../config/constants";
import { round } from "../../../utils/common";

const LimitContent = (props) => {
  const [limit, setLimit] = useState(0);

   const checkValidInput = (textValue) => {
    return textValue && /^[0-9]*(\.[0-9]{0,3})?$/.test(textValue);
  };

  const getValidAmount = (amount) => {
    if (parseFloat(amount) > 0) {
      return amount;
    }

    return 1.000
  };

  const calculateSendingAmount = (value) => {
    const amount = getValidAmount(value);

    if (amount && checkValidInput(amount)) {
      return setLimit(amount);
    }

    return setLimit(
     round(amount, 3)
    );
  };

  return (<View style={styles.bottomSheetContainer}>
    <CustomIcon
      name="close"
      size={16}
      onPress={props.onDismiss}
      style={styles.close}
    />
    <Text style={styles.bottomSheetTitle}>new_tally_text</Text>
    <TextInput
      maxLength={9}
      numberOfLines={1}
      returnKeyType="done"
      keyboardType="numeric"
      style={styles.textInput}
      value={limit? limit : ''}
      onChangeText={(text) => calculateSendingAmount(text)}
   placeholder={limit? round(limit,3) : 'my_limit_text'}
    />
    <Button
      title='next_text'
      onPress={() => {
        props.onNext({ limit: limit })
      }}
      style={styles.button}
    />
  </View>);
}


LimitContent.propTypes = {
  onNext: PropTypes.func.isRequired,
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
    fontSize: 25,
    fontWeight: '400',
    fontFamily: 'inter',
    color: colors.black,
  },
  textInput: {
    borderWidth: 1,
    borderColor: '#BBBBBB',
    paddingHorizontal: 12,
    paddingVertical: 0,
    width: '100%',
    borderRadius: 6,
    marginTop: 40,
    height: 40,
  },
  button: {
    backgroundColor: 'blue',
    borderColor: 'blue',
    width: '100%',
    borderRadius: 40,
    height: 45,
    alignItems: 'center',
    justifyContent: 'center',
    bottom: 0,
    position: 'absolute',
    marginVertical: 24,
    marginBottom:40,
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

export default LimitContent;

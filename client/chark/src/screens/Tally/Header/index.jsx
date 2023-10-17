import React from 'react';
import PropTypes from 'prop-types';
import { View, StyleSheet, TouchableWithoutFeedback, Image } from 'react-native';

import { colors } from '../../../config/constants';

import CustomText from '../../../components/CustomText';

const Header = (props) => {
  return (
    <View style={styles.header}>
      <TouchableWithoutFeedback
        onPress={props.onClick}
      >
        <View>
          {props.leftIcon}
        </View>
      </TouchableWithoutFeedback>

      <CustomText as="h3" style={styles.headerText}>
        {props.title}
      </CustomText>

      <TouchableWithoutFeedback
        onPress={props.onClick}
      >
        <View>
          {props.rightIcon}
        </View>
      </TouchableWithoutFeedback>
    </View>
  )
}

const styles = StyleSheet.create({
  header: {
    margin: 20,
    flexDirection: 'row',
    justifyContent: 'space-between',
    alignItems: 'center',
  },
  headerText: {
    color: colors.gray300,
  },
});

Header.propTypes = {
  title: PropTypes.string.isRequired,
  onClick: PropTypes.func.isRequired,
  icon: PropTypes.any,
}

export default Header;

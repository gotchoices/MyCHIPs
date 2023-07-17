import React from 'react';
import PropTypes from 'prop-types';
import { View, StyleSheet, TouchableWithoutFeedback, Image } from 'react-native';

import { colors } from '../../../config/constants';

import CustomText from '../../../components/CustomText';

const Header = (props) => {
  return (
    <View style={styles.header}>
      <CustomText as="h2" style={styles.headerText}>
        {props.title}
      </CustomText>

      <TouchableWithoutFeedback
        onPress={props.onClick}
      >
        <View>
          {props.icon}
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
    color: colors.white,
  },
});

Header.propTypes = {
  title: PropTypes.string.isRequired,
  onClick: PropTypes.func.isRequired,
  icon: PropTypes.any.isRequired,
}

export default Header;

import React from 'react';
import PropTypes from 'prop-types';
import {
  View,
  StyleSheet,
  TouchableWithoutFeedback,
  Image,
  TouchableOpacity,
} from 'react-native';

import {colors} from '../../../config/constants';

import CustomText from '../../../components/CustomText';

const Header = props => {
  return (
    <View style={styles.header}>
      <TouchableOpacity
        style={{
          height: 50,
          width: 50,
          alignItems: 'flex-start',
          justifyContent: 'center',
        }}
        onPress={props.onClick}>
        <View>{props.leftIcon}</View>
      </TouchableOpacity>

      <CustomText as="h3" style={styles.headerText}>
        {props.title}
      </CustomText>

      <TouchableOpacity
        style={{
          height: 50,
          width: 50,
          alignItems: 'flex-end',
          justifyContent: 'center',
        }}
        onPress={props.onNavigateToNotification}>
        <View>{props.rightIcon}</View>
      </TouchableOpacity>
    </View>
  );
};

const styles = StyleSheet.create({
  header: {
    margin: 20,
    marginHorizontal: 15,
    height: 50,
    flexDirection: 'row',
    justifyContent: 'space-between',
    alignItems: 'center',
  },
  headerText: {
    color: colors.gray300,
    fontWeight: 'bold',
    fontSize: 20,
    textAlign: 'center',
    paddingTop: 10,
  },
});

Header.propTypes = {
  title: PropTypes.string.isRequired,
  onClick: PropTypes.func.isRequired,
  icon: PropTypes.any,
  onNavigateToNotification: PropTypes.func.isRequired,
};

export default Header;

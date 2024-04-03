import React from 'react';
import PropTypes from 'prop-types';
import { 
  View,
  Text,
  StyleSheet,
} from 'react-native';

import { colors } from '../../../config/constants';

const Header = (props) => {
  return (
    <View style={styles.header}>
      {!!props.children && (
        <View style={styles.headerIcon}>
          {props.children}
        </View>
      )}
      <Text style={styles.headerText}>
        {props.headerText}
      </Text>
    </View>
  )
}

const font = {
  fontFamily: 'inter',
  fontWeight: '500',
}

const styles = StyleSheet.create({
  header: {
    flexDirection: 'row',
    justifyContent: 'center',
  },
  headerIcon: {
    position: 'absolute',
    left: 10,
    top: 2,
  },
  headerText: {
    ...font,
    fontSize: 18,
    color: colors.gray300
  },
});

Header.propTypes = {
  headerText: PropTypes.string.isRequired,
  children: PropTypes.node,
}

export default Header;

import React from 'react';
import {
  View,
  StyleSheet,
} from 'react-native'
import PropTypes from 'prop-types';

import BackIcon from '../../../../assets/svg/ic_back.svg';

const Header = (props) => {
  return (
    <View style={styles.header}>
      <BackIcon 
        style={styles.backIcon} 
        onPress={props.onBackPress}
      />
      
      {props.children}
    </View>
  )
}

const styles = StyleSheet.create({
  header: {
    marginTop: 8,
    alignItems: 'center',
    justifyContent: 'center',
  },
  backIcon: {
    position: 'absolute',
    left: 0,
  },
});

Header.propTypes = {
  onBackPress: PropTypes.func.isRequired,
}

export default Header;

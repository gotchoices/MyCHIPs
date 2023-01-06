import React from 'react';
import PropTypes from 'prop-types';
import {
  View,
  Text,
  StyleSheet,
  TouchableWithoutFeedback,
} from 'react-native';
import Icon from 'react-native-vector-icons/FontAwesome';

import { colors } from '../../../config/constants';
import HelpText from '../../../components/HelpText';

const Header = (props) => {
  return (
    <View style={styles.header}>
      <HelpText
        label={props.title}
        helpText={props.helpText}
        style={styles.title}
      />

      <TouchableWithoutFeedback 
        onPress={props.onEditPress}
      >
        <View style={{ padding: 4 }}>
          <Icon
            name="edit"
            size={15}
            color={colors.quicksilver}
          />
        </View>
      </TouchableWithoutFeedback>
    </View>
  )
}

const styles = StyleSheet.create({
  header: {
    flexDirection: 'row',
    justifyContent: 'space-between',
    paddingVertical: 21,
    paddingHorizontal: 16,
    borderBottomWidth: 1,
    borderBottomColor: colors.brightgray,
  },
  title: {
    color: colors.black,
    fontWeight: '700',
    fontSize: 15,
  },
});

Header.propTypes = {
  title: PropTypes.string.isRequired, 
  helpTExt: PropTypes.string,
  onEditPress: PropTypes.func,
}

export default Header;

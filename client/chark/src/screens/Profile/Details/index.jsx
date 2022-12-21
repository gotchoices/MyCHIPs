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
import Header from './Header';
import HelpText from '../../../components/HelpText';

const Details = (props) => {
  return (
    <View style={styles.container}>
      <Header 
        title={props.title}
        helpText={props.helpText}
        onEditPress={props.onEditPress}
      />

      <View>
        {
          props.items.map((item, index) => (
            <View key={index} style={styles.itemRow}>
              <Text style={styles.item}>{item[props.rowField]}</Text>

              {
                props.primaryField && item[props.primaryField] && (
                  <Text style={styles.primary}>
                    Primary
                  </Text>
                )
              }
            </View>
          ))
        }
      </View>
    </View>
  )
}

const styles = StyleSheet.create({
  container: {
    backgroundColor: colors.white,
  },
  itemRow: {
    flexDirection: 'row',
    justifyContent: 'space-between',
    paddingHorizontal: 16,
    paddingVertical: 13,
    borderBottomWidth: 1,
    borderBottomColor: colors.brightgray,
  },
  item: {
    fontSize: 14,
    fontWeight: '400',
    color: colors.dimgray,
  },
  primary: {
    color: colors.blue,
    fontWeight: '600',
  },
});

Details.propTypes = {
  title: PropTypes.string.isRequired, 
  helpText: PropTypes.string, 
  rowField: PropTypes.string.isRequired,
  primaryField: PropTypes.string,
  items: PropTypes.arrayOf(PropTypes.object).isRequired,
  onEditPress: PropTypes.func,
}

export default Details;

import React from 'react';
import PropTypes from 'prop-types';
import { View, Text, StyleSheet } from 'react-native';

import { colors } from '../../../config/constants';
import HelpText from '../../../components/HelpText';

const AddressItem = (props) => {
  return (
    <View style={styles.container}>
      <View>
        <HelpText
          style={styles.help}
          label={props.title ?? ''}
          helpText={props.helpText}
        />
      </View>

      <View>
        {
          !props.addresses?.length && (
            <Text>No {props.title}</Text>
          )
        }

        {
          props.addresses.map((address) => (
            <Text style={styles.address} key={`${address.addr_ent}-${address.addr_seq}`}>
              {buildAddress(address)}
            </Text>
          ))
        }
      </View>
    </View>
  )
}

function buildAddress(address) {
  const {
    addr_spec = '',
    city = '',
    state = '',
    country = '',
  } = address;
  const arr = [addr_spec, city, state, country]

  return arr.join(', ');
}

const styles = StyleSheet.create({
  container: {
    borderBottomWidth: 1,
    borderBottomColor: colors.brightgray,
    padding: 16,
  },
  help: {
    fontWeight: '400',
    fontSize: 12,
  },
  address: {
    fontSize: 15,
    marginBottom: 5,
  }
});

AddressItem.propTypes = {
  title: PropTypes.string.isRequired,
  helpText: PropTypes.string,
  addresses: PropTypes.array.isRequired,
}

export default AddressItem;

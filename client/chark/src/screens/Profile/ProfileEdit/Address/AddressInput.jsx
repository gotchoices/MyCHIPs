import React from 'react';
import PropTypes from 'prop-types';
import {
  StyleSheet,
  Text,
  View,
  TouchableWithoutFeedback,
} from 'react-native';
import Icon from 'react-native-vector-icons/FontAwesome';

import { colors } from '../../../../config/constants';
import HelpTextInput from '../../../../components/HelpTextInput';

const AddressInput = (props) => {
  const address = props.address;

  const onChange = (field) => {
    return (value) => {
      props.onChange(field, value);
    }
  }

  const onRemove = () => {
  }

  return (
    <View style={styles.container}>
      <View style={styles.header}>
        <Text style={styles.address}>
          { address?.addr_seq ? address?.addr_spec : 'New Address' }
        </Text>

        <TouchableWithoutFeedback onPress={onRemove}>
          <Icon
            size={16}
            name="trash-o"
            color={colors.quicksilver}
          />
        </TouchableWithoutFeedback>
      </View>

      <View style={styles.inputSection}>
        <View style={styles.row}>
          <View style={{ width: '60%', marginRight: '3%' }}>
            <HelpTextInput
              label={'Address 1'}
              value={address.addr_spec ?? ''}
              onChange={onChange('addr_spec')}
            />
          </View>

          <View style={{ width: '37%' }}>
            <HelpTextInput
              label={'City'}
              value={address.city ?? ''}
              onChange={onChange('city')}
            />
          </View>
        </View>

        <View style={styles.row}>
          <View style={{ width: '32%', marginRight: '3%' }}>
            <HelpTextInput
              label={'State'}
              value={address.state ?? ''}
              onChange={onChange('state')}
            />
          </View>

          <View style={{ width: '31%', marginRight: '3%' }}>
            <HelpTextInput
              label={'Postal Code'}
              value={address.pcode ?? ''}
              onChange={onChange('pcode')}
            />
          </View>

          <View style={{ width: '31%' }}>
            <HelpTextInput
              label={'Country'}
              value={address.country ?? ''}
              onChange={onChange('country')}
            />
          </View>
        </View>
      </View>
    </View>
  )
}

const styles = StyleSheet.create({
  container: {
    padding: 10,
    //backgroundColor: colors.white,
  },
  header: {
    paddingVertical: 8,
    paddingHorizontal: 8,
    backgroundColor: colors.snow,
    flexDirection: 'row',
    justifyContent: 'space-between',
  },
  row: {
    flexDirection: 'row',
  }
});

AddressInput.propTypes = {
  address: PropTypes.object,
  onChange: PropTypes.func,
}

export default AddressInput;

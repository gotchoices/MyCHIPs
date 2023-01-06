import React from 'react';
import PropTypes from 'prop-types';
import {
  StyleSheet,
  Text,
  View,
  TouchableWithoutFeedback,
} from 'react-native';
import Icon from 'react-native-vector-icons/FontAwesome';
import { Picker } from '@react-native-picker/picker';

import { colors } from '../../../../config/constants';
import HelpText from '../../../../components/HelpText';
import HelpTextInput from '../../../../components/HelpTextInput';

const AddressInput = (props) => {
  const address = props.address;

  const onChange = (field) => {
    return (value) => {
      props.onChange(field, value);
    }
  }

  const onRemove = () => {
    props?.onRemove();
  }

  return (
    <View style={styles.container}>
      <View style={styles.header}>
        <TouchableWithoutFeedback onPress={onRemove}>
          <View style={{ padding: 5 }}>
            <Icon
              size={16}
              name="trash-o"
              color={colors.quicksilver}
            />
          </View>
        </TouchableWithoutFeedback>
      </View>

      <View style={styles.inputSection}>
        <View style={styles.row}>
          <View style={{ width: '60%', marginRight: '3%' }}>
            <HelpTextInput
              inputStyle={styles.input}
              label={'Address 1'}
              value={address.addr_spec ?? ''}
              onChange={onChange('addr_spec')}
            />
          </View>

          <View style={{ width: '37%' }}>
            <HelpTextInput
              label={'City'}
              inputStyle={styles.input}
              value={address.city ?? ''}
              onChange={onChange('city')}
            />
          </View>
        </View>

        <View style={styles.row}>
          <View style={{ width: '32%', marginRight: '3%' }}>
            <HelpTextInput
              label={'State'}
              inputStyle={styles.input}
              value={address.state ?? ''}
              onChange={onChange('state')}
            />
          </View>

          <View style={{ width: '31%', marginRight: '3%' }}>
            <HelpTextInput
              inputStyle={styles.input}
              label={'Postal Code'}
              value={address.pcode ?? ''}
              onChange={onChange('pcode')}
            />
          </View>

          <View style={{ width: '31%' }}>
            <HelpTextInput
              inputStyle={styles.input}
              label={'Country'}
              value={address.country ?? ''}
              onChange={onChange('country')}
            />
            {/*
            <HelpText
              style={{ fontWeight: '400', fontSize: 12 }}
              label={'Country'}
              helpText={''}
            />

            <Picker
              mode="dropdown"
              selectedValue={address.country ?? ''}
              style={styles.input}
              onValueChange={onChange('country')}
            >
              { 
                props.countries?.map((country) => (
                  <Picker.Item key={country.code} label={country.comm_name} value={country.code} />
                ))
              }
            </Picker>
            */}
          </View>
        </View>
      </View>
    </View>
  )
}

const styles = StyleSheet.create({
  container: {
    margin: 10,
    padding: 10,
    borderWidth: 1,
    borderRadius: 5,
    borderColor: '#ddd',
  },
  header: {
    paddingVertical: 8,
    paddingHorizontal: 8,
    flexDirection: 'row',
    justifyContent: 'flex-end',
  },
  row: {
    flexDirection: 'row',
  },
  input: {
    backgroundColor: colors.antiflashwhite,
  },
});

AddressInput.propTypes = {
  address: PropTypes.object.isRequired,
  onChange: PropTypes.func.isRequired,
  countries: PropTypes.array,
  onRemove: PropTypes.func,
}

export default AddressInput;

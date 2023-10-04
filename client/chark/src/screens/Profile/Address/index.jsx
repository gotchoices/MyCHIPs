import React, { useMemo, useState } from 'react';
import { View, StyleSheet } from 'react-native';
import { useSelector } from 'react-redux';

import { colors } from '../../../config/constants';
import useMessageText from '../../../hooks/useMessageText';

import AddressItem from './AddressItem';
import Header from '../Details/Header';

const Address = (props) => {
  const { addresses } = useSelector(state => state.profile);
  const { messageText } = useMessageText();
  const addrVText = messageText?.addr_v ?? {};
  const addrFlatText = messageText?.addr_v_flat ?? {};

  const addressObj = useMemo(() => {
    const mail = [];
    const physical = [];
    const birth = [];

    addresses?.forEach((address) => {
      if(address.addr_type === 'mail') {
        mail.push(address)
      }

      if(address.addr_type === 'phys') {
        physical.push(address)
      }

      if(address.addr_type === 'birth') {
        birth.push(address)
      }
    })

    return {
      mail,
      physical,
      birth,
    }
  }, [addresses])

  const _addresses = [
    {
      title: addrFlatText?.mail_addr?.title ?? '',
      helpText: addrFlatText?.mail_addr?.help ?? '',
      items: addressObj?.mail ?? [],
    },
    {
      title: addrFlatText?.phys_addr?.title ?? '',
      helpText: addrFlatText?.phys_addr?.help ?? '',
      items: addressObj?.physical ?? [],
    },
    {
      title: 'Birth Address',
      helpText: addrFlatText?.birth_addr?.help ?? '',
      items: addressObj?.birth?.length ? [addressObj?.birth?.[0]] : [],
    },
  ];

  const onEditPress = () => {
    props.navigation.navigate('ProfileEdit', {
      profileType: 'address',
      title: 'Edit Addresses',
    })
  }

  return (
    <View style={styles.container}>
      <Header 
        title={addrVText?.addr_spec?.title ?? ''}
        helpText={addrVText?.addr_spec?.help ?? ''}
        onEditPress={onEditPress}
      />

      <View>
        {
          _addresses.map((address, index) => (
            <AddressItem
              key={index}
              title={address.title}
              helpText={address.helpText}
              addresses={address.items}
            />
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

export default Address;

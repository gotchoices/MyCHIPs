import React, { useMemo, useState } from 'react';
import { View, Text, StyleSheet } from 'react-native';

import { colors } from '../../../config/constants';
import useProfile from '../../../hooks/useProfile';
import useMessageText from '../../../hooks/useMessageText';

import AddressItem from './AddressItem';
import Header from '../Details/Header';

const Address = (props) => {
  const { addresses } = useProfile();
  const { messageText } = useMessageText();
  const profileText = messageText?.profile ?? {};

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
      title: profileText?.mail_addr?.title ?? '',
      helpText: profileText?.mail_addr?.help ?? '',
      items: addressObj?.mail ?? [],
    },
    {
      title: profileText?.phys_addr?.title ?? '',
      helpText: profileText?.phys_addr?.help ?? '',
      items: addressObj?.physical ?? [],
    },
    {
      title: 'Birth Address',
      helpText: profileText?.birth_addr?.help ?? '',
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
        title="Addresses"
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

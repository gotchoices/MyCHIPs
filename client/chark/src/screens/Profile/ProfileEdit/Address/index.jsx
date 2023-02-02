import React, { useState, useEffect } from 'react';
import { View, Text, ScrollView, StyleSheet, TouchableWithoutFeedback } from 'react-native';
import Icon from 'react-native-vector-icons/FontAwesome';
import Toast from 'react-native-toast-message';

import { colors } from '../../../../config/constants';
import { request, getAddresses } from '../../../../services/profile';
import { random } from '../../../../utils/common';
import useCurrentUser from '../../../../hooks/useCurrentUser';
import useProfile from '../../../../hooks/useProfile';
import useSocket from '../../../../hooks/useSocket';

import AddressInput from './AddressInput';
import HelpText from '../../../../components/HelpText';
import Button from '../../../../components/Button';

const Address = (props) => {
  const { addresses, setAddresses, lang } = useProfile();
  const { user } = useCurrentUser();
  const [updating, setUpdating] = useState(false);
  const [mail, setMail] = useState([]);
  const [physical, setPhysical] = useState([]);
  const [birth, setBirth] = useState({});
  const [countries, setCountries] = useState([]);
  const [itemsToRemove, setItemsToRemove] = useState([]);

  const user_ent = user?.curr_eid;

  //useEffect(() => {
    //const spec = {
      //fields: ['comm_name', 'code'],
      //view: ['mychips.country'],
    //}

    //request(wm, `country_ref_${random(1000)}`, 'select', spec).then(response => {
      //console.log('hello', response)
      //setCountries(response);
    //})
  //}, [])

  useEffect(() => {
    const _mail = [];
    const _physical = [];
    const _birth = [];

    addresses?.forEach((address) => {
      const {
        addr_ent,
        addr_seq,
        addr_type,
        addr_spec,
        state,
        city,
        pcode,
        country,
      } = address;

      const obj = {
        addr_ent,
        addr_seq,
        addr_spec,
        addr_type,
        state,
        city,
        pcode,
        country,
      }

      if(address.addr_type === 'mail') {
        _mail.push(obj)
      }

      if(address.addr_type === 'phys') {
        _physical.push(obj)
      }

      if(address.addr_type === 'birth') {
        _birth.push(obj);
      }


      setMail(_mail);
      setPhysical(_physical);
      if(!_birth?.length) {
        setBirth({
          addr_ent: user_ent,
          addr_spec: '',
          addr_type: 'birth',
          state: '',
          city: '',
          pcode: '',
          country: '',
        });
      } else {
        setBirth(_birth[0]);
      }
    })
  }, [addresses])

  const onSave = () => {
    setUpdating(true);

    const items = [
      ...mail,
      ...physical,
      birth
    ];
    const promises = [];

    items?.forEach((item) => {
      if(item.addr_seq) {
        const spec = {
          fields: item,
          view: 'mychips.addr_v_me',
          where: {
            addr_seq: item.addr_seq,
            addr_ent: item.addr_ent,
          }
        }

        promises.push(
          request(wm, `mail_update_${random(1000)}`, 'update', spec)
        )
      } else {
        const spec = {
          fields: item,
          view: 'mychips.addr_v_me',
        }
        promises.push(
          request(wm, `mail_update_${random(1000)}`, 'insert', spec)
        )
      }
    })

    if(itemsToRemove.length) {
      itemsToRemove.forEach((seq) => {
        const spec = {
          view: 'mychips.addr_v_me',
          where: {
            addr_seq: seq,
            addr_ent: user_ent,
          },
        }

        promises.push(
          request(wm, `remove_addr_${random(1000)}`, 'delete', spec)
        )
      })
    }

    Promise.all(promises).then(() => {
      Toast.show({
        type: 'success',
        text1: 'Changes saved successfully.',
        position: 'bottom',
      });

      updateAddressList();
    }).finally(() => {
      setUpdating(false);
    })
  }

  const updateAddressList = () => {
    getAddresses(wm, user_ent).then((response) => {
      setAddresses(response);
    })
  }

  const getChangedInput = (address, field, value) => {
    const _address = { ...address };
    _address[field] = value;
    return _address;
  }

  const onChange = (type, index) => {
    return (field, value) => {
      if(type === 'mail') {
        const address = mail[index];
        const _mail = [...mail];
        _mail[index] = getChangedInput(address, field, value) ;
        setMail(_mail)
      } else if(type === 'phys') {
        const address = physical[index];
        const _physical = [...physical];
        _physical[index] = getChangedInput(address, field, value) ;
        setPhysical(_physical)
      }
    }
  }

  const onBirthChange = (field, value) => {
    setBirth({
      ...birth,
      [field]: value,
    });
  }

  const addItem = (type) => {
    return () => {
      const address = {
        addr_ent: user_ent,
        addr_spec: '',
        state: '',
        city: '',
        pcode: '',
        country: '',
        addr_type: type,
      }

      if(type === 'mail') {
        setMail([
          ...mail,
          address,
        ]);
      } else if(type === 'phys') {
        setPhysical([
          ...physical,
          address,
        ]);
      }
    }
  }

  const removeItem = (type, index) => {
    return () => {
      let items = [];

      if(type === 'mail') {
        items = mail;
      } else if(type === 'phys') {
        items = physical;
      }

      const itemToRemove = items[index];
      const _items = items.filter((item, idx) => index !== idx) ;

      if(type === 'mail') {
        setMail(_items);
      } else if(type === 'phys') {
        setPhysical(_items);
      }

      if(itemToRemove?.addr_seq) {
        setItemsToRemove(itemToRemove.addr_seq);
      }

    }
  }

  return (
    <ScrollView style={{ marginBottom: 55 }}>
      <View style={styles.addressSection}>
        <View style={styles.header}>
          <HelpText
            label={lang?.mail_addr?.title ?? ''}
            helpText={lang?.mail_addr?.help}
            style={styles.title}
          />
        </View>

        {
          mail?.map((_mail, index) => (
            <AddressInput
              key={_mail.addr_seq ?? index}
              address={_mail}
              onChange={onChange('mail', index)}
              onRemove={removeItem('mail', index)}
            />
          ))
        }

        <TouchableWithoutFeedback onPress={addItem('mail')}>
          <View style={styles.addButton}>
            <Icon
              name="plus-square"
              size={15}
              color={colors.blue}
            />
            <Text style={{ color: colors.blue, marginLeft: 6 }}>Add New</Text>
          </View>
        </TouchableWithoutFeedback>
      </View>

      <View style={styles.addressSection}>
        <View style={styles.header}>
          <HelpText
            label={lang?.phys_addr?.title ?? ''}
            helpText={lang?.phys_addr?.help}
            style={styles.title}
          />
        </View>

        {
          physical.map((_physical, index) => (
            <AddressInput
              key={_physical.addr_seq ?? index}
              address={_physical}
              onChange={onChange('phys', index)}
              onRemove={removeItem('phys', index)}
            />
          ))
        }

        <TouchableWithoutFeedback onPress={addItem('phys')}>
          <View style={styles.addButton}>
            <Icon
              name="plus-square"
              size={15}
              color={colors.blue}
            />
            <Text style={{ color: colors.blue, marginLeft: 6 }}>Add New</Text>
          </View>
        </TouchableWithoutFeedback>
      </View>

      <View style={styles.addressSection}>
        <View style={styles.header}>
          <HelpText
            label={'Birth Address'}
            helpText={undefined}
            style={styles.title}
          />
        </View>

        <AddressInput
          address={birth}
          onChange={onBirthChange}
        />

      </View>

      <View style={{ marginBottom: 16, marginHorizontal: 8, }}>
        <Button
          onPress={onSave}
          disabled={updating}
          title="Save Changes"
        />
      </View>
    </ScrollView>
  )
}

const styles = StyleSheet.create({
  addressSection: {
    margin: 10,
    backgroundColor: colors.white,
  },
  header: {
    padding: 10,
  },
  title: {
    color: colors.black,
    fontSize: 16,
    fontWeight: 'bold',
  },
  addButton: {
    margin: 10,
    flexDirection: 'row',
    justifyContent: 'center',
    alignItems: 'center',
    padding: 8,
    borderRadius: 5,
    backgroundColor: colors.white,
    borderWidth: 1,
    borderColor: colors.blue ,
    marginBottom: 32,
  }
})

export default Address;

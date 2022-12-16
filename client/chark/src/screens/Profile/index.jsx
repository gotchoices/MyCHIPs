import React, { useState, useEffect } from 'react';
import {
  View,
  StyleSheet,
  ScrollView,
  TextInput,
  Text,
  Button,
  TouchableOpacity,
} from 'react-native';
import Icon from 'react-native-vector-icons/FontAwesome';

import { colors } from '../../config/constants';

import useCurrentUser from '../../hooks/useCurrentUser';
import Avatar from './Avatar';
import HelpTextInput from '../../components/HelpTextInput';
import Comm from './Comm';

const Profile = (props) => {
  const [avatar, setAvatar] = useState(undefined);
  const [tax_id, setTax_id] = useState('');
  const [country, setCountry] = useState('');
  const [born_date, setBorn_date] = useState('');
  const [updatingSSN, setUpdatingSSN] = useState(false);
  const [userLang, setuserLang] = useState({});
  const [addrLang, setAddrLang] = useState({});

  const { user } = useCurrentUser();

  const [profile, setProfile] = useState({
    email: '',
    phone: '',
    mail: '',
    phys: '',
    birth: '',
    birthAddress: '',
  });

  useEffect(() => {
    props.wm.newLanguage('eng')
    props.wm.register('users_lang', 'mychips.users_v_me', (data, err) => {
      if (err) {
        return;
      }

      setuserLang(data?.col ?? {});
    })

    props.wm.register('addr_lang', 'base.addr_v_flat', (data, err) => {
      if (err) {
        return;
      }

      setAddrLang(data?.col ?? {});
    })

  }, [])

  useEffect(() => {
    const user_ent = user?.curr_eid;
    getTaxCountryAndBirth(user_ent);
    getAddress(user_ent);
  }, [])

  const getTaxCountryAndBirth = (user_ent) => {
    const spec = {
      fields: ['user_ent', 'tax_id', 'born_date', 'country'],
      view: 'mychips.users_v_me',
      where: {
        user_ent,
      }
    }

    props.wm.request('_user_ref', 'select', spec, (response) => {
      const user = response?.[0];
      setBorn_date(user?.born_date ?? '');
      setCountry(user?.country ?? '');
      setTax_id(user?.tax_id ?? '');
    })

  }

  const getAddress = (user_ent) => {
    const addrSpec = {
      fields: ['addr_spec', 'addr_type'],
      view: 'mychips.addr_v_me',
      where: {
        user_ent,
      }
    }

    props.wm.request('_addr_ref', 'select', addrSpec, response => {
      const addr = new Set(['phys', 'mail', 'birth'])
      const addrObj =  {};
      response?.forEach((res) => {
        if(addr.has(res.addr_type)) {
          addrObj[res.addr_type] = res.addr_spec;
        }

        setProfile((prev) => {
          return {
            ...prev,
            ...addrObj,
          }
        })
      });
    });

  }

  const onChange = (name) => {
    return (value) => {
      setProfile({
        ...profile,
        [name]: value,
      });
    }
  }

  const saveComm = () => {
    const user_ent = user?.curr_eid;

    const spec = {
      fields: [
      {
        comm_spec: '101-101-1011',
        comm_type: 'phone',
        comm_ent: user_ent,
      },
      {
        comm_spec: '101-101-1011',
        comm_type: 'phone',
        comm_ent: user_ent,
      },
      ],
      view: 'mychips.comm_v_me',
    }

    props.wm.request('_comm_ref', 'insert', spec, (data) => {
      console.log(data)
    })

  }

  const saveTaxCountryAndBirth = () => {
    setUpdatingSSN(true);
    const spec = {
      fields: {
        tax_id,
        born_date,
        country,
      },
      where: {
        user_ent,
      },
      view: 'mychips.users_v_me',
    }

    props.wm.request('_tax_ref', 'update', spec, (data) => {
      setUpdatingSSN(false);
    })

  }

  return (
    <ScrollView style={{ marginBottom: 55 }}>
      <View style={styles.wrapper}>
        <View style={{ marginBottom: 24 }}>
          <Avatar
            avatar={avatar}
            setAvatar={setAvatar}
          />
        </View>

        <Comm
          wm={props.wm}
        />

      </View>

      <View style={styles.wrapper}>
        <HelpTextInput
          value={tax_id}
          onChange={setTax_id}
          label={userLang?.tax_id?.title}
          helpText={userLang?.tax_id?.help}
        />

        <HelpTextInput
          value={country}
          onChange={setCountry}
          label={userLang?.country?.title}
          helpText={userLang?.country?.help}
        />

        <HelpTextInput
          value={born_date}
          onChange={setBorn_date}
          label={userLang?.born_date?.title}
          helpText={userLang?.born_date?.help}
        />

        <Button 
          title="Save"
          disabled={updatingSSN}
          onPress={saveTaxCountryAndBirth} 
        />
      </View>

      <View style={styles.wrapper}>
        <HelpTextInput
          onChange={() => {}}
          label={addrLang?.mail_addr?.title}
          helpText={addrLang?.mail_addr?.help}
        />

        <HelpTextInput
          onChange={() => {}}
          label={addrLang?.phys_addr?.title}
          helpText={addrLang?.phys_addr?.help}
        />

        <View style={styles.formControl}>
          <HelpTextInput
            onChange={() => {}}
            label={'Birth Address'}
          />
        </View>

        <Button title="Save" onPress={() => {}} />
      </View>

    </ScrollView>
  )
}

const styles = StyleSheet.create({
  wrapper: {
    flex: 1,
    margin: 10,
    padding: 10,
    backgroundColor: '#fff',
  },
  formControl: {
    marginVertical: 10,
  },
  label: {
    fontWeight: 'bold',
    marginBottom: 8,
  },
  input: {
    backgroundColor: '#F2F4F7',
  },
});

export default Profile;


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

import Avatar from './Avatar';
import HelpTextInput from '../../components/HelpTextInput';
let pktId = 1;

const Profile = (props) => {
  const [user_ent, setUser_ent] = useState();
  const [avatar, setAvatar] = useState(undefined);
  const [tax_id, setTax_id] = useState('');
  const [country, setCountry] = useState('');
  const [born_date, setBorn_date] = useState('');
  const [updatingSSN, setUpdatingSSN] = useState(false);
  const [userLang, setuserLang] = useState({});
  const [addrLang, setAddrLang] = useState({});
  const [commLang, setCommLang] = useState({});

  const [profile, setProfile] = useState({
    email: '',
    phone: '',
    mail: '',
    phys: '',
    birth: '',
    birthAddress: '',
  });

  useEffect(() => {
    props.wm.request(pktId++, 'select', {
      view: 'base.ent_v',
      table: 'base.curr_eid',
      params: []
    }, data => {
      setUser_ent(data?.[0]?.curr_eid)
      })
  }, [])

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

    props.wm.register('comm_lang', 'base.comm_v_flat', (data, err) => {
      if (err) {
        return;
      }

      setCommLang(data?.col ?? {});
    })
  }, [])

  useEffect(() => {
    if(user_ent) {
      getTaxCountryAndBirth(user_ent);
      getAddress(user_ent);
      getComm(user_ent);
    }

  }, [user_ent])

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

  const getComm = (user_ent) => {
    const commSpec = {
      fields: ['comm_type', 'comm_spec'],
      view: 'mychips.comm_v_me',
      where: {
        user_ent,
      }
    }

    // Comm
    props.wm.request('_comm_ref', 'select', commSpec, response => {
      const comm = new Set(['email', 'phone'])
      const commObj =  {};
      response?.forEach((res) => {
        if(comm.has(res.comm_type)) {
          commObj[res.comm_type] = res.comm_spec;
        }

        setProfile((prev) => {
          return {
            ...prev,
          ...commObj,
          }
        })
      })
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

        <HelpTextInput
          onChange={() => {}}
          label={commLang?.email_comm?.title}
          helpText={commLang?.email_comm?.help}
        />

        <HelpTextInput
          onChange={() => {}}
          label={commLang?.phone_comm?.title}
          helpText={commLang?.phone_comm?.help}
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


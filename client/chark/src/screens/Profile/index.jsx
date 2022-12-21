import React, { useState, useEffect, useMemo } from 'react';
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
import useProfile from '../../hooks/useProfile';
import Avatar from './Avatar';
import Details from './Details';
import PersonalBio from './PersonalBio';
import Address from './Address';

const Profile = (props) => {
  const [avatar, setAvatar] = useState(undefined);
  const [tax_id, setTax_id] = useState('');
  const [country, setCountry] = useState('');
  const [born_date, setBorn_date] = useState('');
  const [updatingSSN, setUpdatingSSN] = useState(false);
  const [userLang, setuserLang] = useState({});
  const [addrLang, setAddrLang] = useState({});

  const { user } = useCurrentUser();
  const { communications, lang, personal } = useProfile();

  const [profile, setProfile] = useState({
    email: '',
    phone: '',
    mail: '',
    phys: '',
    birth: '',
    birthAddress: '',
  });

  useEffect(() => {
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

  const emails = useMemo(() => {
    return communications.filter((comm) => {
      return comm.comm_type === 'email';
    })
  }, [communications])

  const phones = useMemo(() => {
    return communications.filter((comm) => {
      return comm.comm_type === 'phone';
    })
  }, [communications])

  const onEditPress = (profileType, title) => {
    return () => {
      props.navigation.navigate('ProfileEdit', {
        profileType,
        title,
      })
    }
  } 

  return (
    <ScrollView style={{ marginBottom: 55 }}>
      <View style={styles.container}>
        <View style={styles.avatar}>
          <Avatar />

          <Text style={{ color: colors.black, marginTop: 16, fontSize: 18, fontWeight: 'bold', alignSelf: 'center' }}>
            {personal?.cas_name}
          </Text>
        </View>

        <View style={{ marginBottom: 16 }}>
          <Details
            title={lang?.email_comm?.title ?? ''}
            helpText={lang?.email_comm?.help ?? ''}
            rowField="comm_spec"
            primaryField="comm_prim"
            items={emails}
            onEditPress={onEditPress('email', 'Edit Email')}
          />
        </View>

        <View style={{ marginBottom: 16 }}>
          <Details
            title={lang?.phone_comm?.title ?? ''}
            helpText={lang?.phone_comm?.help ?? ''}
            rowField="comm_spec"
            primaryField="comm_prim"
            items={phones}
            onEditPress={onEditPress('phone', 'Edit Phone')}
          />
        </View>

        <View style={{ marginBottom: 16 }}>
          <PersonalBio
            navigation={props.navigation}
          />
        </View>

        <View style={{ marginBottom: 16 }}>
          <Address
          />
        </View>
      </View>
    </ScrollView>
  )
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
    margin: 10,
    padding: 10,
  },
  avatar: {
    padding: 16,
    marginBottom: 12,
    backgroundColor: colors.white,
  }
});

export default Profile;


import React, { useState, useEffect } from 'react';
import {
  View,
  StyleSheet,
  ScrollView,
  TextInput,
  Text,
  Button,
} from 'react-native';

import Avatar from './Avatar';

const Profile = (props) => {
  const [avatar, setAvatar] = useState(undefined);
  const [profile, setProfile] = useState({
    email: '',
    phone: '',
    mail: '',
    phys: '',
    birth: '',
    socialSecurityNumber: '',
    birthAddress: '',
  });

  useEffect(() => {
    const spec = {
      fields: ['user_ent'],
      view: 'mychips.users_v_me',
      where: {}
    }

    const commSpec = {
      fields: ['comm_type', 'comm_spec'],
      view: 'mychips.comm_v_me',
      where: {}
    }

    const addrSpec = {
      fields: ['addr_spec', 'addr_type'],
      view: 'mychips.addr_v_me',
      where: {}
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

    // Address
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

  }, [])

  const onChange = (name) => {
    return (value) => {
      setProfile({
        ...profile,
        [name]: value,
      });
    }
  }

  const onSave = () => {
    // save profile picture 
    /*
    if(avatar) {
      fetch(avatar)
        .then((response) => {
          const blob = response.blob();
          const spec = {
            fields: {
              file_data: blob,
              file_cmt: 'Test',
              file_type: 'photo',
            },
            view: 'mychips.file_v_me',
          }

          props.wm.request('_profile_image', 'insert', spec, data => {
            console.log(data)
          });
        })
    }
    */

    // Comm 
    const commSpec = {
      fields: [
        {
          comm_type: 'email' ,
          comm_spc: profile.email,
        },
        {
          comm_type: 'phone' ,
          comm_spec: profile.phone,
        },
      ],
      view: 'mychips.comm_v_me',
    }

    props.wm.request('_comm_ref', 'update', commSpec, data => {
      console.log(data, 'data')
    });

    // Address save
    const addrSpec = {
      fields: [
        {
          addr_type: 'mail' ,
          //addr_spec: profile.mail,
          addr_spec: 'Mailing addr',
        },
        {
          addr_type: 'phys' ,
          //addr_spec: profile.phys,
          addr_spec: 'Physical addr',
        },
      ],
      view: 'mychips.addr_v_me',
    }

    props.wm.request('_addr_ref', 'update', addrSpec, data => {
      console.log(data, 'data')
    });
  }

  return (
    <ScrollView style={{ marginBottom: 55 }}>
      <View style={styles.container}>
        <View style={{ marginBottom: 24 }}>
          <Avatar
            avatar={avatar}
            setAvatar={setAvatar}
          />
        </View>

        <View style={styles.formControl}>
          <Text style={styles.label}>Email</Text>
          <TextInput 
            style={styles.input}
            value={profile.email}
            onChangeText={onChange('email')}
          />
        </View>

        <View style={styles.formControl}>
          <Text style={styles.label}>Phone</Text>
          <TextInput 
            style={styles.input}
            value={profile.phone}
            onChangeText={onChange('phone')}
          />
        </View>

        <View style={styles.formControl}>
          <Text style={styles.label}>Mailing Address</Text>
          <TextInput 
            style={styles.input}
            value={profile.mail}
            onChangeText={onChange('mail')}
          />
        </View>

        <View style={styles.formControl}>
          <Text style={styles.label}>Physical Address</Text>
          <TextInput 
            style={styles.input}
            value={profile.phys}
            onChangeText={onChange('phys')}
          />
        </View>

        <View style={styles.formControl}>
          <Text style={styles.label}>Social Security Number</Text>
          <TextInput 
            style={styles.input}
            onChangeText={onChange('socialSecurityNumber')}
          />
        </View>

        <View style={styles.formControl}>
          <Text style={styles.label}>Birth date</Text>
          <TextInput 
            style={styles.input}
            onChangeText={onChange('birthDate')}
          />
        </View>

        <View style={styles.formControl}>
          <Text style={styles.label}>Birth Address</Text>
          <TextInput 
            style={styles.input}
            value={profile.birth}
            onChangeText={onChange('birth')}
          />
        </View>

        <Button title="Save" onPress={onSave} />
      </View>
    </ScrollView>
  )
}

const styles = StyleSheet.create({
  container: {
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


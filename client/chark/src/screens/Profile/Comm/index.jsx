import React, { useState, useEffect } from 'react';
import {
  View,
  StyleSheet,
  TextInput,
  Text,
  Button,
  TouchableWithoutFeedback
} from 'react-native';

import { colors } from '../../../config/constants';
import useCurrentUser from '../../../hooks/useCurrentUser';
import HelpText from '../../../components/HelpText';

let pkt = 1;
const Comm = (props) => {
  const { user } = useCurrentUser();
  const user_ent = user?.curr_eid;

  const [updating, setUpdating] = useState(false);
  const [commLang, setCommLang] = useState({});
  const [emailKeys, setEmailKeys] = useState([]);
  const [emailByKey, setEmailByKey] = useState({});
  const [phoneKeys, setPhoneKeys] = useState([]);
  const [phoneByKey, setPhoneByKey] = useState({});

  const onEmailChange = (key, value) => {
    setEmailByKey({
      ...emailByKey,
      [key]: {
        ...emailByKey[key],
        email: value,
      }
    })
  }

  const onPhoneChange = (key, value) => {
    setPhoneByKey({
      ...phoneByKey,
      [key]: {
        ...phoneByKey[key],
        phone: value,
      }
    })
  }

  useEffect(() => {
    getComm(user_ent);

    props.wm.register('comm_lang', 'base.comm_v_flat', (data, err) => {
      if (err) {
        return;
      }

      setCommLang(data?.col ?? {});
    })
  }, [])

  const getComm = (user_ent) => {
    const commSpec = {
      fields: ['comm_type', 'comm_spec', 'comm_seq'],
      view: 'mychips.comm_v_me',
      where: {
        comm_ent: user_ent,
      }
    }

    // Comm
    props.wm.request('_comm_ref', 'select', commSpec, response => {
      const comm = new Set(['email', 'phone'])
      const commObj =  {};
      const emails = [];
      const phones = [];

      response?.forEach((res) => {
        if(res.comm_type === 'email') {
          emails.push({
            email: res.comm_spec,
            seq: res.comm_seq,
          });
        }

        if(res.comm_type === 'phone') {
          phones.push({
            phone: res.comm_spec,
            seq: res.comm_seq,
          });
        }

        const _emailKeys = [];
        const _emailByKey = [];
        emails.forEach((email, index) => {
          const key = `email_${index}`
          _emailKeys.push(key);
          _emailByKey[key] = email;
        })

        const _phoneKeys = [];
        const _phoneByKey = [];
        phones.forEach((phone, index) => {
          const key = `email_${index}`
          _phoneKeys.push(key);
          _phoneByKey[key] = phone;
        })

        setEmailKeys(_emailKeys)
        setEmailByKey(_emailByKey)
        setPhoneKeys(_phoneKeys)
        setPhoneByKey(_phoneByKey)
      })
    });
  }

  const addEmail = () => {
    const key = `email_${emailKeys.length}`
    setEmailKeys([...emailKeys, key])
    setEmailByKey({
      ...emailByKey,
      [key]: {
        email: '',
      }
    })
  }

  const addPhone = () => {
    const key = `phone_${phoneKeys.length}`
    setPhoneKeys([...phoneKeys, key])
    setPhoneByKey({
      ...phoneByKey,
      [key]: {
        phone: '',
      }
    })
  }

  const saveComm = () => {
    const promises = [];

    emailKeys.forEach((key) => {
      if(!emailByKey[key]) {
        return;
      }

      if(emailByKey[key]?.seq) {
        const spec = {
          fields: {
            comm_type: 'email',
            comm_spec: emailByKey?.[key]?.email
          },
          view: 'mychips.comm_v_me',
          where: {
            comm_ent: user_ent,
            comm_seq: emailByKey[key].seq,
          }
        }

        promises.push(
          insertOrUpdateComm(pkt++, 'update', spec)
        )
      } else {
        const spec = {
          fields: {
            comm_ent: user_ent,
            comm_type: 'email',
            comm_spec: emailByKey?.[key]?.email
          },
          view: 'mychips.comm_v_me',
        }
        promises.push(
          insertOrUpdateComm(pkt++, 'insert', spec)
        )
      }
    })

    phoneKeys.forEach((key) => {
      if(!phoneByKey[key]) {
        return;
      }

      if(phoneByKey[key]?.seq) {
        const spec = {
          fields: {
            comm_type: 'phone',
            comm_spec: phoneByKey?.[key]?.phone
          },
          where: {
            comm_ent: user_ent,
            comm_seq: phoneByKey[key].seq,
          },
          view: 'mychips.comm_v_me',
        }

        promises.push(
          insertOrUpdateComm(pkt++, 'update', spec)
        )
      } else {
        const spec = {
          fields: {
            comm_type: 'phone',
            comm_spec: phoneByKey?.[key]?.phone,
            comm_ent: user_ent,
          },
          view: 'mychips.comm_v_me',
        }
        promises.push(
          insertOrUpdateComm(pkt++, 'insert', spec)
        )
      }
    })

    setUpdating(true);
    Promise.all(promises).catch(console.log).finally(() => {
      setUpdating(false);
    })
  }

  const insertOrUpdateComm = (uniqueId, action, spec) => {
    return new Promise((resolve) => {
      props.wm.request(uniqueId, action, spec, (data) => {
        resolve(data);
      })
    })
  }

  return (
    <View>
      <View style={styles.formControl}>
        <HelpText
          label={commLang?.email_comm?.title}
          helpText={commLang?.email_comm?.help}
        />

        {
          emailKeys.map((key) => (
            <TextInput 
              key={key}
              style={styles.input}
              value={emailByKey[key]?.email}
              onChangeText={(value) => onEmailChange(key, value)}
            />
          ))
        }

        <View style={{ width: '40%' }}>
          <Button
            title="Add"
            onPress={addEmail}
          />
        </View>
      </View>

      <View style={styles.formControl}>
        <HelpText
          label={commLang?.phone_comm?.title}
          helpText={commLang?.phone_comm?.help}
        />

        {
          phoneKeys.map((key) => (
            <TextInput 
              style={styles.input}
              value={phoneByKey[key]?.phone}
              onChangeText={(value) => onPhoneChange(key, value)}
            />
          ))
        }

        <View style={{ width: '40%' }}>
          <Button
            title="Add"
            onPress={addPhone}
          />
        </View>
      </View>

        <Button
          title="Save"
          onPress={saveComm}
          disabled={updating}
        />
    </View>

  )
}

const styles = StyleSheet.create({
  formControl: {
    marginVertical: 10,
  },
  input: {
    backgroundColor: colors.gray100,
    marginBottom: 8,
  },
});

export default Comm;

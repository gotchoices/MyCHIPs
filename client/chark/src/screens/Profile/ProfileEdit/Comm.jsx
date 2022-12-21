import React, { useState, useEffect } from 'react';
import {
  View,
  StyleSheet,
  TextInput,
  Text,
  Button,
  TouchableWithoutFeedback,
  ScrollView,
} from 'react-native';
import Icon from 'react-native-vector-icons/FontAwesome';

import { colors } from '../../../config/constants';
import { request } from '../../../services/profile';
import useCurrentUser from '../../../hooks/useCurrentUser';
import useProfile from '../../../hooks/useProfile';
import { getComm } from '../../../services/profile';

import HelpText from '../../../components/HelpText';
import CommInput from './CommInput';

import styles from './styles';

const commText = {
  email: 'Email',
  phone: 'Phone',
};

let pkt = 1;
const Comm = (props) => {
  const profileType = props.profileType
  const { user } = useCurrentUser();
  const { lang, communications, setCommunications } = useProfile();
  const user_ent = user?.curr_eid;
  const [seqToRemove, setSeqToRemove] = useState([]);

  const [loading, setLoading] = useState(false);
  const [updating, setUpdating] = useState(false);
  const [keys, setKeys] = useState([]);
  const [byKey, setByKey] = useState({});

  useEffect(() => {
    const type = props.type
    const emails = communications.filter((comm) => comm.comm_type === profileType);
    const _keys = [];
    const _byKey = {};

    emails.forEach((email, index) => {
      const key = `email_${index}`
      _keys.push(key);
      _byKey[key] = email;
    })

    setKeys(_keys)
    setByKey(_byKey)
  }, [communications])

  const updateCommunicationList = () => {
    getComm(props.wm, user_ent).then((response) => {
      setCommunications(response);
    })
  }

  const onItemChange = (key, value) => {
    setByKey({
      ...byKey,
      [key]: {
        ...byKey[key],
        comm_spec: value,
      }
    })
  }

  const addItem = () => {
    const key = `email_${keys.length}`
    setKeys([...keys, key])
    setByKey({
      ...byKey,
      [key]: {
        email: '',
      }
    })
  }

  const onSave = () => {
    const promises = [];

    keys.forEach((key) => {
      const item = byKey[key]
      if(!item) {
        return;
      }

      if(item?.comm_seq) {
        const spec = {
          fields: {
            comm_type: profileType,
            comm_spec: item?.comm_spec
          },
          view: 'mychips.comm_v_me',
          where: {
            comm_ent: user_ent,
            comm_seq: item.comm_seq,
          }
        }

        promises.push(
          request(props.wm, pkt++, 'update', spec)
        )
      } else {
        const spec = {
          fields: {
            comm_ent: user_ent,
            comm_type: profileType,
            comm_spec: item?.comm_spec,
          },
          view: 'mychips.comm_v_me',
        }
        promises.push(
          request(props.wm, pkt++, 'insert', spec)
        )
      }
    })

    if(seqToRemove.length) {
      seqToRemove.forEach((seq) => {
        const spec = {
          view: 'mychips.comm_v_me',
          where: {
            comm_seq: seq,
            comm_ent: user_ent,
          },
        }

        promises.push(
          request(props.wm, pkt++, 'delete', spec)
        )
      })

    }

    setUpdating(true);
    Promise.all(promises).then(() => {
      updateCommunicationList();
      setSeqToRemove([]);
    }).catch(console.log).finally(() => {
      setUpdating(false);
    })
  }

  const removeItem = (index) => {
    const key = keys[index]
    const item = byKey[key]
    if(!item) {
      return;
    }

    if(item.comm_seq) {
      setSeqToRemove([
        ...seqToRemove,
        item.comm_seq,
      ]);
    }

    const _keys = keys.filter((_, idx) => idx !== index);
    const { [key]: _,  ...rest } = byKey; 
    setKeys(_keys);
    setByKey(rest);
  }

  return (
    <ScrollView style={{ marginBottom: 55 }}>
      <View style={styles.container}>
        <View style={styles.header}>
          <HelpText
            label={lang?.[`${profileType}_comm`]?.title}
            helpText={lang?.[`${profileType}_comm`]?.help}
            style={styles.headerText}
          />

          <TouchableWithoutFeedback>
            <Text style={{ color: colors.blue }}>Change Primary {commText[profileType]}</Text>
          </TouchableWithoutFeedback>
        </View>

        <View style={styles.body}>
          {
            keys.map((key, index) => (
              <CommInput
                key={key}
                id={key}
                index={index}
                item={byKey[key]}
                onChange={onItemChange}
                removeItem={removeItem}
              />
            ))
          }

          <TouchableWithoutFeedback onPress={addItem}>
            <View style={styles.addButton}>
              <Icon
                name="plus-square"
                size={15}
                color={colors.blue}
              />
              <Text style={{ color: colors.blue, marginLeft: 6 }}>Add New</Text>
            </View>
          </TouchableWithoutFeedback>

          <View style={{ marginTop: 8 }}>
            <Button
              title="Save Changes"
              onPress={onSave}
              disabled={updating}
            />
          </View>
        </View>
      </View>
    </ScrollView>
  )
}


export default Comm;

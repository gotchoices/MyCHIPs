import React, { useState } from 'react';
import {
  View,
  Text,
  StyleSheet,
  ScrollView,
  Keyboard,
} from 'react-native';
import Toast from 'react-native-toast-message';

import { colors } from '../../../config/constants';
import { request } from '../../../services/profile';
import useCurrentUser from '../../../hooks/useCurrentUser';
import useProfile from '../../../hooks/useProfile';
import useSocket from '../../../hooks/useSocket';
import useMessageText from '../../../hooks/useMessageText';

import HelpTextInput from '../../../components/HelpTextInput';
import Button from '../../../components/Button';

const PersonalBio = (props) => {
  const { user } = useCurrentUser();
  const { personal, setPersonal } = useProfile();
  const { wm } = useSocket();
  const { messageText } = useMessageText();
  const user_ent = user?.curr_eid;
  const userText = messageText?.users ?? {};

  const [updating, setUpdating] = useState(false);

  const onChange = (field) => {
    return (value) => {
      setPersonal({
        ...personal,
        [field]: value,
      })
    }
  }

  const onSave = () => {
    setUpdating(true);

    const spec = {
      fields: {
        tax_id: personal.tax_id,
        born_date: personal.born_date,
        country: personal.country,
      },
      where: {
        user_ent,
      },
      view: 'mychips.users_v_me',
    }

    request(wm, '_tax_ref', 'update', spec).then(() => {
      Keyboard.dismiss();
    }).catch(err => {
      Toast.show({
        type: 'error',
        text1: err.message,
        position: 'bottom',
      });

    }).finally(() => {
      Toast.show({
        type: 'success',
        messageText1: 'Changes saved successfully.',
        position: 'bottom',
      });
      setUpdating(false);
    })
  }

  return (
    <ScrollView keyboardShouldPersistTaps="handled">
      <View style={styles.container}>
        <View style={styles.header}>
          <Text style={styles.headerText}>Personal Bio</Text>
        </View>

        <View style={styles.body}>
          <HelpTextInput
            value={personal.tax_id}
            onChange={onChange('tax_id')}
            label={userText?.tax_id?.title ?? ''}
            helpText={userText?.tax_id?.help}
          />

          <HelpTextInput
            value={personal.country}
            onChange={onChange('country')}
            label={userText?.country?.title ?? ''}
            helpText={userText?.country?.help}
          />

          <HelpTextInput
            value={personal.born_date}
            onChange={onChange('born_date')}
            label={userText?.born_date?.title ?? ''}
            helpText={userText?.born_date?.help}
          />

          <View style={{ marginTop: 24, marginBottom: 16 }}>
            <Button 
              title="Save Changes"
              disabled={updating}
              onPress={onSave} 
            />
          </View>
        </View>
      </View>
    </ScrollView>
  )
}

const styles = StyleSheet.create({
  container: {
    margin: 10,
    backgroundColor: colors.white,
  },
  header: {
    paddingVertical: 14,
    paddingHorizontal: 10,
    borderBottomWidth: 1,
    borderBottomColor: colors.lightgray,
  },
  headerText: {
    fontSize: 16,
    fontWeight: 'bold',
    color: colors.black,
  },
  body: {
    paddingVertical: 14,
    paddingHorizontal: 10,
  }
})

export default PersonalBio;

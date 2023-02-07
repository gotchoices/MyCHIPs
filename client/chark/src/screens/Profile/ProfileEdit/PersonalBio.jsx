import React, { useState } from 'react';
import {
  View,
  Text,
  StyleSheet,
  ScrollView,
} from 'react-native';
import Toast from 'react-native-toast-message';

import { colors } from '../../../config/constants';
import { request } from '../../../services/profile';
import useCurrentUser from '../../../hooks/useCurrentUser';
import useProfile from '../../../hooks/useProfile';
import useSocket from '../../../hooks/useSocket';

import HelpTextInput from '../../../components/HelpTextInput';
import Button from '../../../components/Button';

const PersonalBio = (props) => {
  const { user } = useCurrentUser();
  const { lang, personal, setPersonal } = useProfile();
  const { wm } = useSocket();
  const user_ent = user?.curr_eid;

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

    request(wm, '_tax_ref', 'update', spec).finally(() => {
      Toast.show({
        type: 'success',
        text1: 'Changes saved successfully.',
        position: 'bottom',
      });
      setUpdating(false);
    })
  }

  return (
    <ScrollView>
      <View style={styles.container}>
        <View style={styles.header}>
          <Text style={styles.headerText}>Personal Bio</Text>
        </View>

        <View style={styles.body}>
          <HelpTextInput
            value={personal.tax_id}
            onChange={onChange('tax_id')}
            label={lang?.tax_id?.title}
            helpText={lang?.tax_id?.help}
          />

          <HelpTextInput
            value={personal.country}
            onChange={onChange('country')}
            label={lang?.country?.title}
            helpText={lang?.country?.help}
          />

          <HelpTextInput
            value={personal.born_date}
            onChange={onChange('born_date')}
            label={lang?.born_date?.title}
            helpText={lang?.born_date?.help}
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

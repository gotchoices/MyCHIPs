import React, { useState, useEffect } from 'react';
import { Picker } from '@react-native-picker/picker';
import {
  View,
  Text,
  Platform,
  NativeModules,
  TouchableWithoutFeedback,
  StyleSheet,
} from 'react-native';

import HelpText from '../../../components/HelpText';
import Button from '../../../components/Button';

import { colors } from '../../../config/constants';
import { languageMap } from '../../../utils/language';
import { random } from '../../../utils/common';
import useSocket from '../../../hooks/useSocket';

const deviceLocale =
  Platform.OS === 'ios'
  ? NativeModules.SettingsManager.settings.AppleLocale || NativeModules.SettingsManager.settings.AppleLanguages[0] 
  : NativeModules.I18nManager.localeIdentifier;

const deviceLanguage = languageMap[deviceLocale]?.language;

const fallbackLanguages = [
  {
    code: 'fin',
    eng_name: 'Finnish',
  },
  {
    code: 'eng',
    eng_name: 'English',
  },
];

const Language = (props) => {
  const [preferredLanguage, setPreferredLanguage] = useState(deviceLanguage ?? 'eng');
  const [languages, setLanguages] = useState([]);
  const { wm } = useSocket();

  useEffect(() => {
    wm.request(`language_ref_${random(1000)}`, 'select', {
      view: 'base.language_v',
      fields: ['code', 'eng_name', 'tables'],
      where: {
        oper: 'notnull',
        left: 'tables',
      },
    }, data => {
      setLanguages(data ?? fallbackLanguages)
    })
  }, [])

  const onSave = () => {
    wm.newLanguage(preferredLanguage);
    props.onCancel();
  }

  return (
    <View style={styles.container}>
      <View style={styles.header}>
        <HelpText
          style={{ color: colors.black }}
          label="Language"
        />
      </View>

      <View style={styles.body}>
        <Picker
          style={styles.input}
          selectedValue={preferredLanguage}
          mode="dropdown"
          onValueChange={(item) => {
            setPreferredLanguage(item);
          }}
        >
          {
            languages.map((language) => (
              <Picker.Item key={language.code} label={language.eng_name} value={language.code} />
            ))
          }
        </Picker>

        <View style={styles.action}>
          <View style={styles.actionItem}>
            <Button
              title="Cancel"
              style={styles.cancel}
              onPress={props.onCancel}
              textColor={colors.blue}
            />
          </View>

          <View style={styles.actionItem}>
            <Button
              title="Save changes"
              onPress={onSave}
            />
          </View>
        </View>
      </View>

    </View>
  )
}

const styles = StyleSheet.create({
  container: {
    width: '100%',
    paddingVertical: 10,
    backgroundColor: colors.white,
  },
  header: {
    padding: 10,
    marginBottom: 10,
    borderBottomWidth: 1,
    borderBottomColor: colors.lightgray,
  },
  body: {
    margin: 10,
  },
  input: {
    marginBottom: 16,
    backgroundColor: colors.antiflashwhite,
  },
  action: {
    flexDirection: 'row',
  },
  actionItem: {
    width: '48%',
  },
  cancel: {
    borderWidth: 1,
    borderColor: colors.blue,
    backgroundColor: colors.white,
    marginRight: '4%',
  },
});

export default Language;

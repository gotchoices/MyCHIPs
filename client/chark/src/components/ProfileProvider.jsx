import React, { useState, useEffect } from 'react';
import { NativeModules } from 'react-native';
import AsyncStorage from '@react-native-async-storage/async-storage'

import ProfileContext from '../context/ProfileContext';

import { languageMap } from '../utils/language';

const deviceLanguage =
  Platform.OS === 'ios'
    ? NativeModules.SettingsManager.settings.AppleLocale || NativeModules.SettingsManager.settings.AppleLanguages[0]
    : NativeModules.I18nManager.localeIdentifier;

const ProfileProvider = ({ children }) => {
  const [preferredLanguage, setPreferredLanguage] = useState({
    name: languageMap[deviceLanguage]?.name ?? '',
    code: languageMap[deviceLanguage]?.language,
  });

  const [preferredCurrency, setPreferredCurrency] = useState({
    name: '',
    code: '',
  });

  const [personal, setPersonal] = useState({});
  const [filter, setFilter] = useState({});

  useEffect(() => {
    AsyncStorage.getItem("filterData").then(data => {
      if (data) {
        try {
          const currentFilter = JSON.parse(data);
          setFilter(currentFilter);
        } catch (ex) {

        }
      } else {
        const initialFilter = {
          offer: { title: "Offers", selected: true, status: 'offer' },
          draft: { title: "Drafts", selected: true, status: 'draft' },
          void: { title: "Voids", selected: true, status: 'void' },
        }
        storeFilter(initialFilter)
      }
    })
  }, [setFilter]);

  const storeFilter = (data) => {
    AsyncStorage.setItem("filterData", JSON.stringify(data)).then(() => {
      setFilter(data);
    });
  }

  return (
    <ProfileContext.Provider value={{
      preferredCurrency,
      setPreferredCurrency,
      preferredLanguage,
      setPreferredLanguage,
      personal,
      setPersonal,
      filter,
      setFilter,
    }}>
      {children}
    </ProfileContext.Provider>
  )
}

export default ProfileProvider;

import React, { useEffect, useState } from 'react';
import { View, TouchableOpacity, TouchableWithoutFeedback, Text, StyleSheet, Image, Platform, NativeModules } from 'react-native';
import Icon from 'react-native-vector-icons/FontAwesome';

import { colors } from '../../config/constants';
import useCurrentUser from '../../hooks/useCurrentUser';
import useProfile from '../../hooks/useProfile';
import { getPersonal } from '../../services/profile';
import { languageMap } from '../../utils/language';
import useSocket from '../../hooks/useSocket';

import Language from './Language';
import CenteredModal from '../../components/CenteredModal';
import Button from '../../components/Button';

import profileImg from '../../../assets/profile.png';

const deviceLanguage =
  Platform.OS === 'ios'
  ? NativeModules.SettingsManager.settings.AppleLocale || NativeModules.SettingsManager.settings.AppleLanguages[0]
  : NativeModules.I18nManager.localeIdentifier;

const Setting = (props) => {
  const [isLangModalVisible, setIsLangModalVisible] = useState(false);
  const { wm } = useSocket();

  const { user } = useCurrentUser();
  const user_ent = user?.curr_eid;
  const {
    personal,
    setPersonal,
  } = useProfile();

  useEffect(() => {
    getPersonal(wm, user_ent).then(data => {
      setPersonal(data);
    });
  }, [])

  const onProfilePress = () => {
    props.navigation.navigate('Profile');
  }

  const showModal = () => {
    setIsLangModalVisible(true);
  }

  const onCancel = () => {
    setIsLangModalVisible(false);
  }

  return (
    <View style={styles.container}>
      <View style={styles.profile}>
        <Image
          style={styles.profileImage}
          source={profileImg} 
        />

        <Text style={styles.name}>
          {personal?.cas_name}
        </Text>

        <Button
          title="Edit profile"
          onPress={onProfilePress}
        />

      </View>

      <View style={styles.menu}>
        <View>
          <Text style={styles.menuTitle}>
            Language Preference
          </Text>

          <Text style={styles.language}>
            {languageMap[deviceLanguage]?.name ?? ''} ({deviceLanguage})
          </Text>
        </View>

        <TouchableWithoutFeedback
          onPress={showModal}
        >
          <Icon
            name="edit"
            size={15}
            color={colors.quicksilver}
          />
        </TouchableWithoutFeedback>
      </View>

      <CenteredModal
        isVisible={isLangModalVisible}
        onClose={onCancel}
      >
        <Language onCancel={onCancel} />
      </CenteredModal>
    </View>
  )
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
    padding: 16,
  },
  profile: {
    paddingVertical: 24,
    alignItems: 'center',
    backgroundColor: colors.white,
    marginBottom: 8,
  },
  profileImage: {
    width: 100,
    height: 100,
    borderRadius: 50,
  },
  name: {
    color: colors.black,
    marginVertical: 16,
    fontSize: 18,
    fontWeight: 'bold',
    alignSelf: 'center',
  },
  menu: {
    padding: 12,
    backgroundColor: colors.white,
    flexDirection: 'row',
    alignItems: 'center',
    justifyContent: 'space-between',
  },
  menuTitle: {
    paddingBottom: 5,
    color: colors.black,
    fontWeight: '600',
  },
});

export default Setting;

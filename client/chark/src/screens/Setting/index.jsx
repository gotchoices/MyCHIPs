import React, { useEffect, useState } from 'react';
import { View, TouchableOpacity, TouchableWithoutFeedback, Text, StyleSheet, Image, Platform, NativeModules, ScrollView } from 'react-native';
import Icon from 'react-native-vector-icons/FontAwesome';
import AsyncStorage from '@react-native-async-storage/async-storage'

import { colors } from '../../config/constants';
import useCurrentUser from '../../hooks/useCurrentUser';
import useProfile from '../../hooks/useProfile';
import { languageMap } from '../../utils/language';
import useSocket from '../../hooks/useSocket';
import { useExchange } from '../../hooks/useLanguage';

import Language from './Language';
import CenteredModal from '../../components/CenteredModal';
import Button from '../../components/Button';
import GenerateKey from './GenerateKey';
import HelpText from '../../components/HelpText';

import Currency from './Currency';
import ExportKey from './GenerateKey/ExportKey';
import Avatar from '../../components/Avatar';

const deviceLanguage =
  Platform.OS === 'ios'
    ? NativeModules.SettingsManager.settings.AppleLocale || NativeModules.SettingsManager.settings.AppleLanguages[0]
    : NativeModules.I18nManager.localeIdentifier;

const lang = `${languageMap[deviceLanguage]?.name ?? ''} (${deviceLanguage})`;

const Setting = (props) => {
  const [isLangModalVisible, setIsLangModalVisible] = useState(false);
  const [isSelectCurrencyVisible, setIsSelectCurrencyVisible] = useState(false);

  const { wm } = useSocket();
  const exchange = useExchange(wm)

  const { user } = useCurrentUser();
  const user_ent = user?.curr_eid;
  const {
    personal,
    preferredLanguage,
    preferredCurrency,
    avatar,
  } = useProfile();

  // useEffect(() => {
  //   getPersonal(wm, user_ent).then(data => {
  //     setPersonal(data);
  //   });
  // }, [])

  const onProfilePress = () => {
    props.navigation.navigate('Profile');
  }

  const showModal = () => {
    setIsLangModalVisible(true);
  }

  const onCancel = () => {
    setIsLangModalVisible(false);
  }

  const showSelectCurrency = () => {
    setIsSelectCurrencyVisible(true);
  }
  const cancelSelectCurrency = () => {
    setIsSelectCurrencyVisible(false);
  }

  return (
    <ScrollView
      style={styles.container}
      contentContainerStyle={styles.contentContainer}
    >
      <View style={styles.profile}>
        <Avatar style= {styles.profileImage} avatar = {avatar}/>

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
            {preferredLanguage?.name} ({preferredLanguage?.code})
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



      <View style={[styles.menu, { marginTop: 10 }]}>
        <View>
          <HelpText
            label={exchange?.curr?.title ?? ''}
            helpText={exchange?.curr?.help ?? ''}
            style={styles.menuTitle}
          />

          <Text style={styles.language}>
            {
              preferredCurrency?.code
                ? `${preferredCurrency?.name} (${preferredCurrency?.code})`
                : 'None'

            }
          </Text>
        </View>

        <TouchableWithoutFeedback
          onPress={showSelectCurrency}
        >
          <Icon
            name="edit"
            size={15}
            color={colors.quicksilver}
          />
        </TouchableWithoutFeedback>
      </View>

      <View style={[styles.menu, { marginTop: 10 }]}>
        <GenerateKey menuStyle={styles.menuTitle} />
      </View>

      <View style={[styles.menu, { marginTop: 10 }]}>
        <TouchableOpacity
          style={{ width: "100%" }}
          onPress={() => {
            props.navigation.navigate("ImportKey");
          }}
        >
          <Text style={styles.menuTitle}>Import Key</Text>
        </TouchableOpacity>
      </View>

      <View style={[styles.menu, { marginTop: 10 }]}>
        <ExportKey menuStyle={styles.menuTitle} />
      </View>

      <CenteredModal
        isVisible={isLangModalVisible}
        onClose={onCancel}
      >
        <Language onCancel={onCancel} />
      </CenteredModal>

      <CenteredModal
        isVisible={isSelectCurrencyVisible}
        onClose={cancelSelectCurrency}
      >
        <Currency onCancel={cancelSelectCurrency} />
      </CenteredModal>
    </ScrollView>
  )
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
  },
  contentContainer: {
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

import React from 'react';
import {
  View,
  Text,
  StyleSheet,
} from 'react-native';

import { colors } from '../../../config/constants';
import useProfile from '../../../hooks/useProfile';
import useMessageText from '../../../hooks/useMessageText';

import Header from '../Details/Header';
import HelpText from '../../../components/HelpText';

const Item = (props) => {
  return (
    <View style={styles.itemRow}>
      <HelpText
        label={props.title ?? ''}
        helpText={props.helpText ?? ''}
      />
      <Text style={{ fontsize: 15 }}>{props.value}</Text>
    </View>
  )
}


const PersonalBio = (props) => {
  const { personal } = useProfile();
  const { messageText } = useMessageText();

  const onEditPress = () => {
    props.navigation.navigate('ProfileEdit', {
      profileType: 'personal',
      title: 'Edit Personal Bio',
    });
  }

  return (
    <View style={styles.container}>
      <Header
        title="Personal Bio"
        onEditPress={onEditPress}
      />

      <Item
        title={messageText?.tax_id?.title}
        helpText={messageText?.tax_id?.help}
        value={personal?.tax_id}
      />

      <Item
        title={messageText?.country?.title}
        helpText={messageText?.country?.help}
        value={personal?.country}
      />

      <Item
        title={messageText?.born_date?.title}
        helpText={messageText?.born_date?.help}
        value={personal?.born_date}
      />

    </View>
  )
}

const styles = StyleSheet.create({
  container: {
    backgroundColor: colors.white,
  },
  itemRow: {
    paddingHorizontal: 16,
    paddingVertical: 13,
    borderBottomWidth: 1,
    borderBottomColor: colors.brightgray,
  },
})

export default PersonalBio;

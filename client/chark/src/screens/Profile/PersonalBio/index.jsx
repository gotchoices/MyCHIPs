import React from 'react';
import PropTypes from 'prop-types';
import {
  View,
  Text,
  StyleSheet,
  TouchableWithoutFeedback,
} from 'react-native';
import Icon from 'react-native-vector-icons/FontAwesome';

import { colors } from '../../../config/constants';
import useProfile from '../../../hooks/useProfile';
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
  const { personal, lang } = useProfile();

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
        title={lang?.tax_id?.title}
        helpText={lang?.tax_id?.help}
        value={personal?.tax_id}
      />

      <Item
        title={lang?.country?.title}
        helpText={lang?.country?.help}
        value={personal?.country}
      />

      <Item
        title={lang?.born_date?.title}
        helpText={lang?.born_date?.help}
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

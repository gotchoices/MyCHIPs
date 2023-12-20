import React from 'react';
import {
  View,
  ScrollView,
  Text,
  TextInput,
  StyleSheet,
} from 'react-native';

import Header from './Header';
import HelpText from '../../../components/HelpText'
import { ChitIcon } from '../../../components/SvgAssets/SvgAssets';
import SwapIcon from '../../../../assets/svg/swap.svg';
import Button from '../../../components/Button';

import { colors } from '../../../config/constants';

const PendingChitDetail = (props) => {
  const onBack = () => {
    props.navigation.navigate('PendingChits');
  }

  const onSwap = () => {
    console.los('swap')
  }

  return (
    <View style={styles.container}>
      <View style={{ marginBottom: 48 }}>
        <Header onBackPress={onBack}>
          <Text style={styles.headerText}>
            Details
          </Text>
        </Header>
      </View>

      <View style={styles.body}>
        <View style={styles.netWrapper}>
          <View>
            <View style={styles.net}>
              <ChitIcon color={colors.black} height={53} width={26.5}/>
              <Text style={styles.chip}>
                12.01
              </Text>
            </View>

            <Text style={styles.currency}>
              32.68 USD
            </Text>
          </View>

          <SwapIcon 
            style={{ marginLeft: 12 }}
            onPress={onSwap} 
          />
        </View>

        <TextInput
          multiline
          numberOfLines={6}
          value={'tacos'}
          style={[styles.input, styles.comment]}
          onChangeText={() => {}}
        />

        <View style={styles.reference}>
          <HelpText
            style={styles.referenceText}
            label={'Reference'}
          />
        </View>
      </View>

      <View style={styles.action}>
        <Button
          title="Accept"
          onPress={() => {}}
        />

        <Button
          title="Reject"
          style={styles.rejectBtn}
          onPress={() => {}}
        />
      </View>

    </View>
  )
}

const font = {
  fontFamily: 'inter',
  fontWeight: '500',
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
    marginHorizontal: 24,
  },
  headerText: {
    fontSize: 18,
    fontFamily: 'inter',
    fontWeight: '500',
    color: colors.gray300,
  },
  body: {
  },
  netWrapper: {
    flexDirection: 'row',
    justifyContent: 'center',
    alignItems: 'center',
    marginBottom: 32,
  },
  net: {
    flexDirection: 'row',
    alignItems: 'center',
  },
  currency: {
    ...font,
    fontWeight: '400',
    alignSelf: 'flex-end',
    fontSize: 14,
  },
  chip: {
    ...font,
    color: colors.black,
    fontSize: 45,
    marginLeft: 5,
  },
  input: {
    padding: 10,
    borderWidth: 1,
    borderRadius: 5,
    textAlignVertical: 'top',
    borderColor: colors.gray,
    backgroundColor: colors.white,
    marginBottom: 32,
  },
  referenceText: {
    ...font,
    fontSize: 16,
    color: colors.gray300,
  },
  action: {
    bottom: 0,
    marginBottom: 28,
    width: '100%',
    position: 'absolute',
  },
  rejectBtn: {
    marginTop: 10,
    borderColor: colors.red,
    backgroundColor: colors.red,
  }
});

export default PendingChitDetail;

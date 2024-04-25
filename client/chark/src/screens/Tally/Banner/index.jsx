import React, {useMemo} from 'react';
import {
  View,
  Text,
  StyleSheet,
  Dimensions,
  TouchableOpacity,
} from 'react-native';
import {useSelector} from 'react-redux';

import {colors} from '../../../config/constants';
import {isNil} from '../../../utils/common';
import useMessageText from '../../../hooks/useMessageText';

import Header from '../Header';
import Avatar from '../../../components/Avatar';
import {
  ChitIcon,
  FilterSecondIcon,
  VisualIcon,
} from '../../../components/SvgAssets/SvgAssets';
import Activity from '../Activity';
import { getDecimalValue, getIntegerValue } from '../../../utils/user';

const Banner = props => {
  const {avatar, personal} = useSelector(state => state.profile);
  const {messageText} = useMessageText();
  const talliesMeMessageText = messageText?.tallies_v_me?.msg;
  const chitMeText = messageText?.chits_v_me?.col;
  const charkText = messageText?.chark?.msg;

  const navigateToReport = () => {
    props.navigation?.navigate?.('TallyReport');
  };

  const navigateToNotification = () => {
    props.navigation?.navigate?.('Activity');
  };

  const pendingText = useMemo(() => {
    return chitMeText?.status?.values?.find(s => s.value === 'pend');
  }, [chitMeText?.status?.values]);

  const isNetNegative = props.totalNet < 0;
  const hasPendingTotal =
    !isNil(props.totalPendingNet) &&
    props.totalPendingNet != 0.0 &&
    props.totalPendingNet != props.totalNet; // If pending net and total net are equal, then the tally does not have pending chits

  const onFilter = () => {
    props.navigation.navigate('FilterTallyScreen');
  };

  return (
    <View style={styles.container}>
      <Header
        leftIcon={<VisualIcon />}
        title={charkText?.mychips?.title ?? ''}
        onClick={navigateToReport}
        onNavigateToNotification={navigateToNotification}
        rightIcon={<Activity />}
      />

      <View style={{alignItems: 'center', justifyContent: 'center'}}>
        <View style={styles.balanceContainer}>
          <View style={styles.balance}>
            <View style={styles.avatarWrapper}>
              <Avatar avatar={avatar} />
              <Text style={styles.name}>{personal?.cas_name ?? ''}</Text>
            </View>
          </View>
        </View>
      </View>

      <View style={styles.row}>
        <TouchableOpacity style={styles.filterContainer} onPress={onFilter}>
          <FilterSecondIcon />
          <Text style={styles.filterText}>
            {talliesMeMessageText?.sort?.title ?? ''}
          </Text>
        </TouchableOpacity>

        <View style={styles.textWrapper}>
          {/* {hasPendingTotal && (
            <Text style={styles.pending}>
              {pendingText?.title ?? ''} {props.totalPendingNet}
            </Text>
          )} */}

          {!!props.currencyCode && (
            <Text style={styles.amount}>
              {props.currencyCode} {props.totalNetDollar}
            </Text>
          )}

          <View style={{flexDirection: 'row', alignItems: 'center'}}>
            <ChitIcon color={isNetNegative ? colors.red : colors.green} />
            <Text
              style={isNetNegative ? styles.mychipsNetNeg : styles.mychipsNet}>
              {getIntegerValue(props.totalNet)}
            </Text>
            <Text
              style={[
                isNetNegative ? styles.mychipsNetNeg : styles.mychipsNet,
                {
                  textDecorationLine: 'underline',
                  lineHeight: 16,
                  fontSize: 16,
                  paddingBottom: 10,
                },
              ]}>
              {getDecimalValue(props.totalNet)}
            </Text>
          </View>
        </View>
      </View>
    </View>
  );
};

const mychipsNet = {
  marginLeft: 5,
  fontSize: 32,
  fontWeight: '500',
  color: colors.green,
  maxWidth: Dimensions.get('window').width * 0.5,
  fontFamily: 'inter',
};

const font = {
  fontFamily: 'inter',
};

const styles = StyleSheet.create({
  container: {
    marginHorizontal: 10,
  },
  balanceContainer: {
    ...font,
    padding: 16,
    maxWidth: '90%',
    borderRadius: 25,
    overflow: 'hidden',
  },
  balance: {
    flexDirection: 'row',
    alignItems: 'center',
    justifyContent: 'space-between',
  },
  mychipsNet,
  mychipsNetNeg: {
    ...mychipsNet,
    color: colors.red,
  },
  name: {...font, paddingTop: 15, fontSize: 16, fontWeight: '600'},
  avatarWrapper: {marginTop: 20},
  textWrapper: {
    marginBottom: -15,
    marginRight: 10,
    alignItems: 'flex-end',
    justifyContent: 'flex-end',
  },
  amount: {
    ...font,
    fontSize: 16,
    color: colors.gray300,
  },
  pending: {
    ...font,
    fontSize: 12,
  },
  filterContainer: {
    height: 30,
    borderWidth: 1,
    borderRadius: 20,
    paddingVertical: 3,
    flexDirection: 'row',
    alignItems: 'center',
    paddingHorizontal: 12,
    justifyContent: 'center',
    borderColor: colors.white100,
    backgroundColor: colors.white200,
  },
  filterText: {
    fontSize: 12,
    marginStart: 4,
    color: '#636363',
    fontFamily: 'inter',
  },
  row: {
    marginLeft: 10,
    flexDirection: 'row',
    alignItems: 'flex-end',
    justifyContent: 'space-between',
  },
});

export default Banner;

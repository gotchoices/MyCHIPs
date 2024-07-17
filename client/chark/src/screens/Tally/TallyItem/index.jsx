import React, {useEffect, useMemo, useState} from 'react';
import {View, Text, StyleSheet} from 'react-native';
import PropTypes from 'prop-types';

import {colors} from '../../../config/constants';
import {round} from '../../../utils/common';

import Avatar from '../../../components/Avatar';
import {ChitIcon} from '../../../components/SvgAssets/SvgAssets';
import {formatRandomString} from '../../../utils/format-string';
import useMessageText from '../../../hooks/useMessageText';
import {getDecimalValue, getIntegerValue} from '../../../utils/user';

const TallyItem = props => {
  const tally = props.tally;
  const net = round((tally?.net ?? 0) / 1000, 3);
  const pendingNet = tally?.net_pc ? round(tally.net_pc / 1000, 3) : 0;
  const convertedNet = round(net * props.conversionRate, 2);
  const partCert = tally?.part_cert;
  const partName =
    partCert?.type === 'o'
      ? `${partCert?.name}`
      : `${partCert?.name?.first}${
          partCert?.name?.middle ? ' ' + partCert?.name?.middle + ' ' : ''
        } ${partCert?.name?.surname}`;

  const hasPendingChit = !!tally?.net_pc && net != pendingNet;

  const {messageText} = useMessageText();
  const chitMeText = messageText?.chits_v_me?.col;
  const pendingText = useMemo(() => {
    return chitMeText?.status?.values?.find(s => s.value === 'pend');
  }, [chitMeText?.status?.values]);

  return (
    <View style={styles.container}>
      <Avatar style={styles.avatar} avatar={props.image} />

      <View style={{flex: 1}}>
        <Text style={styles.name}>{partName}</Text>
        <Text style={[styles.description, {marginTop: 4}]}>
          {partCert?.chad?.cuid}:{formatRandomString(partCert?.chad?.agent)}
        </Text>
      </View>

      <View style={styles.price}>
        {hasPendingChit && (
          <View style={styles.pendingView}>
            <Text style={styles.pending}>
              {pendingText?.title ?? ''} Chips
            </Text>
          </View>
        )}

        {!!props.currency && (
          <Text style={convertedNet < 0 ? styles.dollarNeg : styles.dollar}>
            {props.currency} {convertedNet}
          </Text>
        )}

        <View style={styles.mychips}>
          <ChitIcon
            color={net < 0 ? colors.red : colors.green}
            height={18}
            width={12}
          />
          <Text style={net < 0 ? styles.mychipsNetNeg : styles.mychipsNet}>
            {getIntegerValue(net)}
          </Text>

          <Text style={net < 0 ? styles.negDecimal : styles.decimal}>
            {getDecimalValue(net)}
          </Text>
        </View>
      </View>
    </View>
  );
};

const font = {
  fontFamily: 'inter',
};

const mychipsNet = {
  fontSize: 22,
  lineHeight: 22,
  fontWeight: '600',
  color: colors.green,
  fontFamily: 'inter',
  marginHorizontal: 2,
};

const styles = StyleSheet.create({
  container: {
    flexDirection: 'row',
    justifyContent: 'space-between',
  },
  profile: {
    flexDirection: 'row',
  },
  avatar: {
    marginRight: 8,
    alignSelf: 'center',
    height: 45,
    width: 45,
    borderRadius: 45 / 2,
  },
  name: {
    ...font,
    fontSize: 16,
    fontWeight: 'bold',
  },
  description: {
    ...font,
    fontSize: 12,
    color: colors.gray500,
  },
  price: {
    ...font,
    alignItems: 'flex-end',
  },
  pending: {
    fontSize: 8,
    color: colors.gray700,
  },
  mychips: {
    flexDirection: 'row',
  },
  mychipsNet,
  mychipsNetNeg: {
    ...mychipsNet,
    color: colors.red,
  },
  dollar: {
    ...font,
    color: colors.gray300,
    fontSize: 10,
    fontWeight: '600',
  },
  dollarNeg: {
    ...font,
    color: colors.gray300,
    fontSize: 10,
    fontWeight: '600',
  },
  pendingView: {
    backgroundColor: colors.white200,
    padding: 5,
    borderRadius: 10,
    marginBottom:2
  },
  decimal: {
    color: colors.green,
    fontSize: 12,
    lineHeight: 12,
    textDecorationLine: 'underline',
  },
  negDecimal: {
    fontSize: 12,
    lineHeight: 12,
    textDecorationLine: 'underline',
    color: colors.red,
  },
});

TallyItem.propTypes = {
  tally: PropTypes.object.isRequired,
  conversionRate: PropTypes.number.isRequired,
  currency: PropTypes.string,
};

export default TallyItem;

import React, { useEffect, useState } from 'react';
import { View, Text, StyleSheet } from 'react-native';
import PropTypes from 'prop-types';

import { colors } from '../../../config/constants';
import { round } from '../../../utils/common';

import Avatar from '../../../components/Avatar';
import { ChitIcon } from '../../../components/SvgAssets/SvgAssets';
import { formatRandomString } from '../../../utils/format-string';

const TallyItem = (props) => {
  const tally = props.tally;
  const net = round((tally?.net ?? 0) / 1000, 3);
  const pendingNet = tally?.net_pc ? round(tally.net_pc / 1000, 3) : 0;
  const convertedNet = round(net * props.conversionRate, 2);
  const partCert = tally?.part_cert;
  const partName = partCert?.type === 'o'
    ? `${partCert?.name}`
    : `${partCert?.name?.first}${partCert?.name?.middle ? ' ' + partCert?.name?.middle + ' ' : ''} ${partCert?.name?.surname}`

  return (
    <View style={styles.container}>

      <Avatar style={styles.avatar} avatar={props.image} />

      <View style={{ flex: 1, }}>
        <Text style={styles.name}>{partName}</Text>
        <Text style={[styles.description, { marginTop: 4 }]}>
          {partCert?.chad?.cid}:{formatRandomString(partCert?.chad?.agent)}
        </Text>
      </View>

      <View style={styles.price}>
        {!!tally?.net_pc && (
          <Text style={styles.pending}>
            {pendingNet}
          </Text>
        )}

        <View style={styles.mychips}>
          <ChitIcon color={net < 0 ? colors.red : colors.green} height={18} width={12} />
          <Text style={net < 0 ? styles.mychipsNetNeg : styles.mychipsNet}>{net}</Text>
        </View>

        {
          !!props.currency && (
            <Text style={convertedNet < 0 ? styles.dollarNeg : styles.dollar}>
              {convertedNet} {props.currency}
            </Text>
          )
        }
      </View>
    </View>
  )
}

const font = {
  fontFamily: 'inter',
}

const mychipsNet = {
  fontSize: 18,
  fontWeight: '600',
  color: colors.green,
  fontFamily: 'inter',
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
  },
  mychips: {
    flexDirection: 'row',
    alignItems: 'center',
  },
  mychipsNet,
  mychipsNetNeg: {
    ...mychipsNet,
    color: colors.red,
  },
  dollar: {
    ...font,
    color: colors.green,
    fontSize: 10,
    fontWeight: '600',
  },
  dollarNeg: {
    ...font,
    color: colors.red,
    fontSize: 10,
    fontWeight: '600',
  },
})

TallyItem.propTypes = {
  tally: PropTypes.object.isRequired,
  conversionRate: PropTypes.number.isRequired,
  currency: PropTypes.string,
}

export default TallyItem;


import React from 'react';
import {
  View,
  Text,
  StyleSheet,
  TouchableWithoutFeedback,
} from 'react-native';
import PropTypes from 'prop-types';
import moment from 'moment';

import { ChitIcon } from '../../../components/SvgAssets/SvgAssets';
import AcceptButton from './AcceptButton';
import RejectButton from './RejectButton';

import { colors } from '../../../config/constants';
import { round } from '../../../utils/common';

const ChitItem = (props) => {
  const isNegative = props.chit.net_pc < 0;

  const net_pc = round((props?.chit?.net_pc ?? 0) / 1000, 3);
  const convertedNet = round(net_pc * props.conversionRate, 2);

  const onPress = () => {
    props.navigation.navigate('PendingChitDetail', {
      chit: props.chit,
    });
  }

  return (
    <View style={styles.container}>
      <TouchableWithoutFeedback
        onPress={onPress}
      >
        <View style={styles.item}>
          <View style={styles.description}>
            <Text style={{ color: colors.black }}>
              Charged you for 
            </Text>

            <Text style={styles.memo}>
              {' ' + (props.chit.memo ?? 'N/A')}
            </Text>
          </View>

          <View style={styles.chit}>
            <ChitIcon color={isNegative ? colors.red : colors.green} />
            <Text style={styles.pend(isNegative)}>
              {net_pc}
            </Text>
          </View>

          <Text style={styles.currency}>
            {convertedNet}
          </Text>
        </View>
      </TouchableWithoutFeedback>

      <View style={styles.action}>
        <Text style={styles.time}>
          {moment(props.chit.chit_date).fromNow(true)}
        </Text>

        <AcceptButton
          json={props.chit?.json_core}
          chit_ent={props.chit?.chit_ent}
          chit_uuid={props.chit?.chit_uuid}
          style={styles.btn}
        />

        <RejectButton
          chit_ent={props.chit?.chit_ent}
          chit_uuid={props.chit?.chit_uuid}
          style={[styles.reject, styles.btn]}
        />
      </View>
    </View>
  )
}

const font = {
  fontFamily: 'inter',
};

const styles = StyleSheet.create({
  container: {
    flexDirection: 'row',
    justifyContent: 'space-between',
    width: '100%',
    borderColor: colors.gray300,
    borderBottomWidth: 0.5,
  },
  item: {
    width: '75%',
    justifyContent: 'center',
  },
  description: {
    flexDirection: 'row',
    marginBottom: 4,
  },
  memo: {
    ...font,
    fontWeight: '700',
    color: colors.black,
  },
  chit: {
    flexDirection: 'row',
    alignItems: 'center',
    marginBottom: 4,
  },
  pend: (isNegative) => ({
    fontSize: 20,
    marginLeft: 4,
    color: isNegative ? colors.red : colors.green,
  }),
  currency: {
    ...font,
    fontSize: 12,
    color: colors.black,
  },
  action: {
    width: '25%'
  },
  time: {
    ...font,
    fontSize: 8,
    marginBottom: 3,
    alignSelf: 'flex-end',
  },
  btn: {
    height: 28,
    marginBottom: 8,
  },
  reject: {
    backgroundColor: colors.red,
    borderColor: colors.red,
  }
});

ChitItem.propTypes = {
  chit: PropTypes.any.isRequired,
  navigation: PropTypes.any,
}

export default ChitItem;

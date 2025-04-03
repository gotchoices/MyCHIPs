import React from 'react';
import {
  View,
  Text,
  StyleSheet,
  TouchableWithoutFeedback,
} from 'react-native';
import PropTypes from 'prop-types';
import moment from 'moment';

import Avatar from '../../../components/Avatar';
import AcceptButton from './AcceptButton';
import RejectButton from './RejectButton';
import { ChitIcon } from '../../../components/SvgAssets/SvgAssets';
import HelpText from '../../../components/HelpText';

import { colors } from '../../../config/constants';
import { round, unitsToChips, formatChipValue, unitsToFormattedChips } from '../../../utils/common';
import useMessageText from '../../../hooks/useMessageText';

const ChitItem = (props) => {
  const isNegative = props.chit.net < 0;
  const { messageText } = useMessageText()
  const talliesMessageText = messageText?.tallies_v_me?.msg;
  const chitsMessageText = messageText?.chits_v_me?.msg;

  const commonText = {
    offer: talliesMessageText?.offer,
    accept: talliesMessageText?.accept,
    approve: chitsMessageText?.approve,
    reject: chitsMessageText?.reject,
    rejected: chitsMessageText?.rejected,
    accepted: chitsMessageText?.approved,
  }

  const net_pc = unitsToFormattedChips(props?.chit?.net ?? 0);
  const convertedNet = round(net_pc * props.conversionRate, 2);

  const chits_msg = messageText?.chits_v_me?.msg;

  const onPress = () => {
    const chit = props?.chit;
    if(chit?.state === 'L.pend') {
      props.navigation.navigate('PendingChitDetail', {
        chit: props.chit,
      });
    } else {
      props.navigation.navigate('ChitDetail', {
        chit_uuid: chit?.chit_uuid,
        chit_ent: chit?.chit_ent,
        chit_idx: chit?.chit_idx,
        chit_seq: chit?.chit_seq,
      });
    }
  }

  let chitTypeLabel = '';
  let chitTypeHelp = '';

  if(props.chit.issuer === props.chit.tally_type) {
    chitTypeLabel = chits_msg?.liability?.title ?? '';
    chitTypeHelp = chits_msg?.liability?.help;
  } else {
    chitTypeLabel = chits_msg?.asset?.title ?? '';
    chitTypeHelp = chits_msg?.asset?.help;
  }

  return (
    <View style={styles.container}>
      <TouchableWithoutFeedback
        onPress={onPress}
      >
        <View style={{ flexDirection: 'row', width: '75%' }}>
          <Avatar style={styles.avatar} avatar={props.avatar} />

          <View style={styles.item}>
            <View style={styles.chitType}>
              <HelpText
                label={chitTypeLabel}
                helpText={chitTypeHelp}
              />
            </View>
            
            {/* Top row with name and amounts */}
            <View style={styles.topRow}>
              {/* Left column - Name */}
              <View style={styles.nameContainer}>
                {props.partnerName ? (
                  <Text style={styles.name} numberOfLines={1}>
                    {props.partnerName}
                  </Text>
                ) : null}
              </View>
              
              {/* Right column - Amounts */}
              <View style={styles.amountsContainer}>
                <View style={styles.chit}>
                  <ChitIcon color={isNegative ? colors.red : colors.green} />
                  <Text style={styles.pend(isNegative)}>
                    {net_pc}
                  </Text>
                </View>
                
                <Text style={styles.currency}>
                  {props.currencyCode} {convertedNet}
                </Text>
              </View>
            </View>
            
            {/* Bottom row - Memo spans full width */}
            <View style={styles.memoContainer}>
              <Text style={styles.memo}>
                {(props.chit.memo ?? '')}
              </Text>
            </View>
          </View>
        </View>
      </TouchableWithoutFeedback>

      <View style={styles.action}>
        <Text style={styles.time}>
          {moment(props.chit.chit_date).fromNow(true)}
        </Text>

        {props.chit?.state === 'L.pend' && (
          <>
            <AcceptButton
              json={props.chit?.json_core}
              chit_ent={props.chit?.chit_ent}
              chit_seq={props.chit?.chit_seq}
              chit_idx={props.chit?.chit_idx}
              style={styles.btn}
              postAccept={props?.postAccept}
              text={commonText}
            />

            <RejectButton
              chit_ent={props.chit?.chit_ent}
              chit_seq={props.chit?.chit_seq}
              chit_idx={props.chit?.chit_idx}
              style={[styles.reject, styles.btn]}
              postReject={props?.postReject}
              text={commonText}
            />
          </>
        )}
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
    paddingVertical: 10,
  },
  item: {
    flex: 1,
    justifyContent: 'center',
  },
  topRow: {
    flexDirection: 'row',
    justifyContent: 'space-between',
    marginBottom: 4,
  },
  nameContainer: {
    flex: 1,
    paddingRight: 8,
  },
  amountsContainer: {
    alignItems: 'flex-end',
  },
  memoContainer: {
    marginTop: 2,
  },
  memo: {
    ...font,
    color: colors.black,
    fontSize: 12,
  },
  chit: {
    flexDirection: 'row',
    alignItems: 'center',
  },
  pend: (isNegative) => ({
    fontSize: 18,
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
  },
  avatar: {
    marginRight: 8,
    alignSelf: 'center',
    height: 60,
    width: 60,
    borderRadius: 60 / 2,
  },
  text: {
    fontFamily: 'inter',
    color: colors.black,
  },
  name: {
    fontFamily: 'inter',
    color: colors.black,
    fontSize: 14,
    fontWeight: '600',
  },
});

ChitItem.propTypes = {
  chit: PropTypes.any.isRequired,
  navigation: PropTypes.any,
  avatar: PropTypes.string,
  conversionRate: PropTypes.number,
  postAccept: PropTypes.func,
  postReject: PropTypes.func,
  partnerName: PropTypes.string,
  currencyCode: PropTypes.string,
}

export default ChitItem;

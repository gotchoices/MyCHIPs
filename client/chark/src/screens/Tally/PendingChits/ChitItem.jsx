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
import { round } from '../../../utils/common';
import useMessageText from '../../../hooks/useMessageText';

const ChitItem = (props) => {
  const isNegative = props.chit.net < 0;
  const { messageText } = useMessageText()
  const talliesMessageText = messageText?.tallies_v_me?.msg;
  const chitsMessageText = messageText?.chits_v_me?.msg;

  const commonText = {
    offer: talliesMessageText?.offer,
    accept: talliesMessageText?.accept,
    reject: talliesMessageText?.reject,
    rejected: chitsMessageText?.rejected,
    accepted: chitsMessageText?.accepted,
  }

  const net_pc = round((props?.chit?.net ?? 0) / 1000, 3);
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

            <View style={styles.description}>
              <Text style={styles.memo}>
                {(props.chit.memo ?? '')}
              </Text>
            </View>

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
    //width: '75%',
    justifyContent: 'center',
  },
  description: {
    flexDirection: 'row',
    marginBottom: 4,
  },
  memo: {
    ...font,
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
    fontWeight: '700',
    textDecorationLine: 'underline',
  },
});

ChitItem.propTypes = {
  chit: PropTypes.any.isRequired,
  navigation: PropTypes.any,
  avatar: PropTypes.string,
  conversionRate: PropTypes.number,
  postAccept: PropTypes.func,
  postReject: PropTypes.func,
}

export default ChitItem;

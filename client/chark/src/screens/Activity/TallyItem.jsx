import React, { useState } from 'react';
import {
  View,
  Text,
  StyleSheet,
  TouchableWithoutFeedback,
} from 'react-native';
import PropTypes from 'prop-types';
import moment from 'moment';
import Toast from 'react-native-toast-message';

import Avatar from '../../components/Avatar';
import AcceptButton from '../Tally/AcceptButton';
import OfferButton from '../Tally/OfferButton';
import Button from '../../components/Button';

import useSocket from '../../hooks/useSocket';
import { colors } from '../../config/constants';
import { refuseTally } from '../../services/tally';
import useMessageText from '../../hooks/useMessageText';

const TallyItem = (props) => {
  const tally = props.tally;
  const { wm } = useSocket();
  const [rejecting, setRejecting] = useState(false);
  const { messageText } = useMessageText();
  const talliesMeText = messageText?.tallies_v_me?.col;

  const canOffer = tally.state === "P.draft";
  const canAccept = tally.state === "P.offer";

  const partCert = tally.part_cert;
  const partName = partCert?.type === 'o'
    ? `${partCert?.name}`
    : `${partCert?.name?.first}${partCert?.name?.middle ? ' ' + partCert?.name?.middle + ' ' : ''} ${partCert?.name?.surname}`

  const onPress = () => {
    props.navigation.navigate('TallyPreview', {
      tally_seq: tally?.tally_seq,
      tally_ent: tally?.tally_ent,
    });
  }

  const onReject = async () => {
    setRejecting(true);
    try {
      await refuseTally(wm, {
        tally_ent: tally.tally_ent,
        tally_seq: tally.tally_seq,
      })

      props?.postOffer?.();

      Toast.show({
        type: "success",
        text1: "Tally refused.",
      });
    } catch(err) {
      Toast.show({
        type: "error",
        text1: err.message,
      });
    } finally {
      setRejecting(false);
    }
  };

  return (
    <View style={styles.container}>
      <TouchableWithoutFeedback
        onPress={onPress}
      >
        <View style={styles.item}>
          <Avatar style={styles.avatar} avatar={props.image} />

          <View style={{ flex: 1, }}>
            <Text style={styles.name}>{partName}</Text>
            <Text style={[styles.description, { marginTop: 4 }]}>
              {talliesMeText?.request?.title ?? ''}
            </Text>
          </View>
        </View>
      </TouchableWithoutFeedback>

      <View style={styles.action}>
        <Text style={styles.time}>
          {moment(tally?.crt_date).fromNow(true)}
        </Text>

        {canAccept && (
          <AcceptButton
            tally={tally}
            postOffer={props.postAccept}
            style={styles.btn}
          />
        )}

        {canOffer && (
          <OfferButton
            tally={tally}
            style={[styles.btn, styles.offerBtn]}
            postOffer={props.postOffer}
          />
        )}

        <Button
          title="reject_text"
          onPress={onReject}
          disabled={rejecting}
          style={[styles.btn, styles.rejectBtn]}
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
    paddingVertical: 10,
  },
  item: {
    width: '75%',
    flexDirection: 'row',
    alignItems: 'center',
  },
  avatar: {
    marginRight: 8,
    alignSelf: 'center',
    height: 60,
    width: 60,
    borderRadius: 60 / 2,
  },
  name: {
    ...font,
    color: colors.black,
    fontSize: 16,
  },
  description: {
    ...font,
    fontSize: 14,
    marginBottom: 4,
    flexDirection: 'row',
    color: colors.gray300,
  },
  action: {
    width: '25%'
  },
  time: {
    ...font,
    fontSize: 8,
    marginBottom: 4,
    alignSelf: 'flex-end',
  },
  btn: {
    height: 28,
    marginBottom: 8,
  },
  offerBtn: {
    marginBottom: 8,
    borderRadius: 40,
    backgroundColor: colors.yellow,
    borderColor: colors.yellow,
  },
  rejectBtn: {
    backgroundColor: colors.red,
    borderColor: colors.red,
  },
});

TallyItem.propTypes = {
  tally: PropTypes.any.isRequired,
  navigation: PropTypes.any,
  postOffer: PropTypes.func,
  postAccept: PropTypes.func,
  image: PropTypes.string,
}

export default TallyItem;

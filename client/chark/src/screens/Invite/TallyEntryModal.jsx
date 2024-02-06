import React from 'react';
import PropTypes from 'prop-types';
import { useSelector } from 'react-redux';
import { View, Text, StyleSheet } from 'react-native';

import Button from '../../components/Button';
import Avatar from '../../components/Avatar';
import HandshakeIcon from '../../../assets/svg/handshake.svg';
import GreenTickIcon from '../../../assets/svg/green_tick.svg';
import CustomIcon from "../../components/CustomIcon";
import OfferButton from '../Tally/OfferButton';
import AcceptButton from '../Tally/AcceptButton';

import { colors } from '../../config/constants';
import useMessageText from '../../hooks/useMessageText';

const TallyEntryModal = (props) => {
  const negotiationData = props.negotiationData;
  const { imagesByDigest } = useSelector(state => state.avatar);
  const { messageText } = useMessageText();

  const talliesMeText = messageText?.tallies_v_me?.col;

  return (
    <View style={{ margin: 20 }}>
      <CustomIcon
        name="close"
        size={16}
        onPress={props.onNeogitationModalClose}
        style={styles.handshake}
      />

      <View style={{ alignItems: 'center' }}>
        <HandshakeIcon />
        <View style={{ flexDirection: 'row' }}>
          <Avatar avatar={imagesByDigest[negotiationData?.data?.tallyType === 'stock' ? negotiationData?.data?.partDigest : negotiationData?.data?.holdDigest]} style={styles.foilAvatar}/>
          <Avatar avatar={imagesByDigest[negotiationData?.data?.tallyType === 'stock' ? negotiationData?.data?.holdDigest : negotiationData?.data?.partDigest]} style={styles.stockAvatar}/>
        </View>

        <Text style={{ fontWeight: '400', fontSize: 30, color: colors.black, fontFamily: 'inter' }}>
          {negotiationData.data?.name}
        </Text>

        <Text style={{ color: colors.gray6 }}>
          {talliesMeText?.tally_start?.title ?? 'wants_to_start_a_tally_with_you'}
        </Text>

        <View style={styles.partLimit}>
          <Text style={{ marginRight: 5, color: colors.gray6 }}>
            part_limit ${negotiationData.data?.limit} 
          </Text>
          <GreenTickIcon />
        </View>
      </View>
      
      {props.shouldShowReview &&
      <Button
        title={talliesMeText?.review?.title ?? 'review'}
        onPress={() => props.onReview(negotiationData?.data?.tally_seq, negotiationData?.data?.tally_ent)}
        textColor={colors.blue}
        style={{ marginBottom: 5, borderRadius: 40, backgroundColor: colors.white }}
      />
    }

      {negotiationData.data?.canAccept && (
        <AcceptButton
          tally={negotiationData.data}
          postOffer={props.postAccept}
          style={{ marginBottom: 5, borderRadius: 40 }}
        />
      )}

      {negotiationData.data?.canOffer && (
        <OfferButton
          tally={negotiationData.data}
          style={{ marginBottom: 5, borderRadius: 40, backgroundColor: colors.yellow, borderColor: colors.yellow }}
          postOffer={props.postOffer}
        />
      )}

    </View>
  )
}

const avatarStyle = {
  width: 70,
  height: 70,
}

const styles = StyleSheet.create({
  handshake: {
    alignSelf: 'flex-end',
    backgroundColor: 'white',
    height: 24,
    width: 24,
    justifyContent: 'center',
    alignItems: 'center',
  },
  partLimit: {
    flexDirection: 'row',
    alignItems: 'center',
    marginTop: 30,
    marginBottom: 15 ,
  },
  foilAvatar: {
    ...avatarStyle,
  },
  stockAvatar: {
    ...avatarStyle,
    zIndex: 3,
    marginLeft: -12,
  },
})

TallyEntryModal.propTypes = {
  negotiationData: PropTypes.object.isRequired,
  onReview: PropTypes.func.isRequired,
  onNeogitationModalClose: PropTypes.func.isRequired,
}

export default TallyEntryModal;

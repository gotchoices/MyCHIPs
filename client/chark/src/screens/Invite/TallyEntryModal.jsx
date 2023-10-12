import React from 'react';
import PropTypes from 'prop-types';
import { useSelector } from 'react-redux';
import { View, Text, StyleSheet } from 'react-native';

import { colors } from '../../config/constants';
import Button from '../../components/Button';
import Avatar from '../../components/Avatar';
import HandshakeIcon from '../../../assets/svg/handshake.svg';
import GreenTickIcon from '../../../assets/svg/green_tick.svg';
import CustomIcon from "../../components/CustomIcon";


const TallyEntryModal = (props) => {
  const negotiationData = props.negotiationData;
  const { imagesByDigest } = useSelector(state => state.avatar);

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
          Wants to start a tally 
        </Text>

        <Text style={{ color: colors.gray6 }}>
          with you
        </Text>

        <View style={styles.partLimit}>
          <Text style={{ marginRight: 5, color: colors.gray6 }}>
            Part limit ${negotiationData.data?.limit} 
          </Text>
          <GreenTickIcon />
        </View>
      </View>
      
      <Button
        title="Review"
        onPress={() => props.onReview(negotiationData?.data?.tally_seq, negotiationData?.data?.tally_ent)}
        textColor={colors.blue}
        style={{ marginBottom: 5, borderRadius: 40, backgroundColor: colors.white }}
      />

      {negotiationData.data?.canAccept && (
        <Button
          title="Accept"
          disabled={props.accepting}
          onPress={() => props.onAccept(negotiationData.data)}
          style={{ marginBottom: 5, borderRadius: 40 }}
        />
      )}

      {negotiationData.data?.canOffer && (
        <Button
          title="Offer"
          disabled={props.offering}
          onPress={() => props.onOffer(negotiationData.data)}
          style={{ marginBottom: 5, borderRadius: 40, backgroundColor: colors.yellow, borderColor: colors.yellow }}
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
  accepting: PropTypes.bool.isRequired,
  offering: PropTypes.bool.isRequired,
  negotiationData: PropTypes.object.isRequired,
  onOffer: PropTypes.func.isRequired,
  onAccept: PropTypes.func.isRequired,
  onReview: PropTypes.func.isRequired,
  onNeogitationModalClose: PropTypes.func.isRequired,
}

export default TallyEntryModal;

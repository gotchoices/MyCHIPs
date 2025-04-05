import React, { useState } from "react";
import { useSelector } from "react-redux";
import {
  View,
  Text,
  StyleSheet,
  Modal,
} from "react-native";

import PropTypes from "prop-types";
import { colors } from "../../config/constants";
import Button from "../../components/Button";
import Avatar from "../../components/Avatar";
import CustomIcon from "../../components/CustomIcon";
import { formatRandomString } from "../../utils/format-string";
import useMessageText from '../../hooks/useMessageText';

const PayModal = (props) => {
  const { imagesByDigest } = useSelector((state) => state.avatar);

  const { messageText } = useMessageText();
  const talliesMeText = messageText?.tallies_v_me?.col;
  const talliesMeMessageText = messageText?.tallies_v_me?.msg;

  const partCert = props.tally?.part_cert;
  const partName = partCert?.type === 'o'
    ? `${partCert?.name}`
    : `${partCert?.name?.first}${partCert?.name?.middle ? ' ' + partCert?.name?.middle + ' ' : ''} ${partCert?.name?.surname}`
  const description = `${partCert?.chad?.cuid}:${formatRandomString(partCert?.chad?.agent)}`

  const onViewTally = () => {
    props.onClose()

    props.navigation.navigate('OpenTallyView', {
      tally_seq: props.tally.tally_seq,
      tally_ent:  props.tally.tally_ent,
    });

  }

  const onPay = () => {
    props.onClose()

    props.navigation.navigate("PaymentDetail", {
      chit_ent: props.tally?.tally_ent,
      tally_uuid: props.tally?.tally_uuid,
      chit_seq: props.tally.tally_seq,
      tally_type: props.tally?.tally_type,
      chad: props.tally?.hold_chad,
    });
  };

  const onRequest = () => {
    props.onClose()

    props.navigation.navigate("RequestDetail", {
      tally_uuid: props.tally?.tally_uuid,
      chit_seq: props.tally?.tally_seq,
      tally_type: props.tally?.tally_type,
    });
  };


  const onViewPendingChits = () => {
    props.onClose();

    props.navigation.navigate('PendingChits', {
      partName,
      description,
      tally_uuid: props?.tally?.tally_uuid,
      conversionRate: props.conversionRate,
    })
  }

  const onViewChitHistory = () => {
    props.onClose()

    props.navigation.navigate("ChitHistory", {
      part_name: partName,
      tally_seq: props?.tally?.tally_seq,
      tally_ent: props?.tally?.tally_ent,
      tally_uuid: props?.tally?.tally_uuid,
      digest: partCert?.file?.[0]?.digest,
      date: props?.tally?.tally_date,
      net: props?.tally?.net,
      net_pc: props?.tally?.net_pc,
      cuid: partCert?.chad?.cuid,
    });
  };

  const onViewTradeSettings = () => {
    props.onClose()

    props.navigation.navigate("TradingVariables", {
      tally_seq: props?.tally?.tally_seq,
      tally_ent: props?.tally?.tally_ent,
      tally_type: props?.tally?.tally_type,
      chad: props?.tally?.hold_chad,
      tally_uuid: props?.tally?.tally_uuid,
    });
  };

  const hasPendingChits = !!props.tally?.net_pc && !!props.tally?.net && (props.tally.net_pc != props.tally.net);

  return (
    <Modal visible={props.visible} transparent onRequestClose={props.onClose}>
      <View style={styles.modalWrapper}>

        <View style={styles.modalView}>
        <View style={styles.row}>
        <CustomIcon
      name="close"
      size={16}
      onPress={props.onClose}
      style={styles.close}
    />
        </View>

          <View style={styles.center}>
            <Avatar style={styles.profileImage} avatar={imagesByDigest?.[props.tally?.part_cert?.file?.[0]?.digest]} />

            <Text style={styles.bottomSheetTitle}>{partName}</Text>
        <Text style={[styles.bottomSheetSub, { marginTop: 4 }]}>{description}</Text>
          </View>

          <View style={{ flex: 1 }} />
          {hasPendingChits && (
            <Button
              textColor={colors.gray300}
              title={talliesMeText?.chits_p?.title ?? 'pending_chits'}
              onPress={onViewPendingChits}
              style={styles.pendingChit}
            />
          )}
          <Button
            textColor="blue"
            title={talliesMeMessageText?.['launch.detail']?.title ?? ''}
            onPress={onViewTally}
            style={styles.secondaryButton}
          />

          <View style={{ flex: 1 }} />
          <Button 
            title={talliesMeMessageText?.['launch.pay']?.title ?? ''}
            onPress={onPay}
            style={styles.button} 
          />

          <View style={{ flex: 1 }} />
          <Button
            title={talliesMeMessageText?.['launch.request']?.title ?? 'request'}
            onPress={onRequest}
            style={styles.button}
          />

          <Button
            style={styles.button}
            onPress={onViewChitHistory}
            title={talliesMeMessageText?.['launch.chits']?.title ?? ''}
          />

          <Button
            style={styles.button}
            title={talliesMeMessageText?.trade?.title ?? 'trading'} 
            onPress={onViewTradeSettings}
          />
        </View>
      </View>
    </Modal>
  );
};

PayModal.propTypes = {
  onClose: PropTypes.func.isRequired,
};

const styles = StyleSheet.create({
  modalWrapper: {
    flex: 1,
    backgroundColor: "rgba(0, 0, 0, 0.3)",
    justifyContent: "flex-end",
  },
  modalView: {
    backgroundColor: colors.white,
    borderTopRightRadius: 30,
    borderTopLeftRadius: 30,
    padding: 35,
    paddingTop: 24,
    shadowColor: "black",
    shadowOffset: {
      width: 2,
      height: 3,
    },
    shadowOpacity: 0.25,
    shadowRadius: 4,
    elevation: 15,
  },
  center: {
    alignItems: "center",
    justifyContent: "center",
  },
  bottomSheetContainer: {
    position: "absolute",
    bottom: 0,
    right: 0,
    height: 600,
    paddingHorizontal: 16,
    paddingVertical: 24,
    alignItems: "center",
  },
  bottomSheetTitle: {
    fontSize: 14,
    paddingTop:20,
    fontWeight: "500",
    fontFamily: "inter",
    color: colors.black,
  },
  bottomSheetSub: {
    fontSize: 12,
    color: "#636363",
    paddingBottom:30,
    fontWeight: "500",
    fontFamily: "inter",
  },
  secondaryButton: {
    backgroundColor: colors.white,
    borderColor: colors.blue,
    marginBottom: 10,
  },
  button: {
    backgroundColor: colors.blue,
    marginBottom: 10,
  },
  close: {
     width: 24,
    height: 24,
   alignSelf: "flex-end",
    alignItems: "center",
    backgroundColor: "white",
    justifyContent: "center",
  },
  pendingChit: {
    height: 45,
    borderWidth: 1,
    marginBottom: 10,
    borderColor: colors.gray9,
    backgroundColor: colors.gray8,
  },
  profileImage:   {
    width: 100,
    height: 100,
    marginRight: 8,
    alignSelf: 'center',
    borderRadius: 100 / 2,
  },
});

export default PayModal;

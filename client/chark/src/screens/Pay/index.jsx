import React, { useState } from "react";
import {
  View,
  Text,
  StyleSheet,
  TouchableOpacity,
  Modal,
  Dimensions,
} from "react-native";

import PropTypes from "prop-types";
import { colors } from "../../config/constants";
import Button from "../../components/Button";
import Avatar from "../../components/Avatar";
import useSocket from "../../hooks/useSocket";
import { useTallyText } from "../../hooks/useLanguage";
import CustomIcon from "../../components/CustomIcon";
import { formatRandomString } from "../../utils/format-string";
import { useSelector } from "react-redux";

const PayModal = (props) => {
  const {
    imagesByDigest,
  } = useSelector((state) => state.openTallies);

  const { wm } = useSocket();
  const tallyText = useTallyText(wm);
  const partCert = props.tally?.part_cert;
  const partName = partCert?.type === 'o'
    ? `${partCert?.name}`
    : `${partCert?.name?.first}${partCert?.name?.middle ? ' ' + partCert?.name?.middle + ' ' : ''} ${partCert?.name?.surname}`
  const description = `${partCert?.chad?.cid}:${formatRandomString(partCert?.chad?.agent)}`

  const onViewTally = () => {

    props.onClose()

    props.navigation.navigate('OpenTallyEdit', {
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

  return (
    <Modal visible={props.visible} transparent>
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
          <Button
            textColor={colors.gray300}
            title="Pending Chits"
            onPress={onViewPendingChits}
            style={styles.pendingChit}
          />
          <Button
            textColor="blue"
            title="View Tally"
            onPress={onViewTally}
            style={styles.secondaryButton}
          />

          <View style={{ flex: 1 }} />
          <Button title="Pay" onPress={onPay} style={styles.button} />

          <View style={{ flex: 1 }} />
          <Button
            title="Request"
            onPress={onRequest}
            style={styles.button}
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
    fontWeight: "500",
    color: "#636363",
    fontFamily: "inter",
    paddingBottom:30,
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
    alignSelf: "flex-end",
    backgroundColor: "white",
    height: 24,
    width: 24,
    justifyContent: "center",
    alignItems: "center",
  },
  pendingChit: {
    backgroundColor: colors.gray8,
    borderColor: colors.gray9,
    borderWidth: 1,
    height: 45,
    marginBottom: 10,
  },
});

export default PayModal;

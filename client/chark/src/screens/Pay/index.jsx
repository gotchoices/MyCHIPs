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
        imageFetchTrigger,
        tallies: tallies,
        imagesByDigest,
        fetching,
      } = useSelector((state) => state.openTallies);

    const { wm } = useSocket();
    const tallyText = useTallyText(wm);

    const [tally, setTally] = useState();
    const [target, setTarget] = useState("");
    const [bound, setBound] = useState("");
    const [reward, setReward] = useState("");
    const [clutch, setClutch] = useState("");

    (() => {
        fetchTally();
      }, [props.tally?.tally_seq, props.tally?.tally_ent]);
    
      const fetchTally = () => {
        setLoading(true);
        fetchTallies(wm, {
          fields: [
            "bound",
            "reward",
            "clutch",
            "tally_seq",
            "tally_uuid",
            "tally_date",
            "status",
            "hold_terms",
            "part_terms",
            "part_cert",
            "tally_type",
            "comment",
            "contract",
            "net",
            'hold_cert',
          ],
          where: {
            tally_ent,
            tally_seq,
          },
        })
          .then((data) => {
            if (data?.length) {
              const _tally = data?.[0];
    
              setTally(_tally);
              setTarget((_tally?.target ?? "").toString());
              setBound((_tally?.bound ?? "").toString());
              setReward((_tally?.reward ?? "").toString());
              setClutch((_tally?.clutch ?? "").toString());
            }
          })
          .catch((e) => {
            console.log("ERROR===>", e);
          })
          .finally(() => {
            setLoading(false);
          });
      };



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
          tally_uuid: props.tally?.tally_uuid,
          chit_seq: props.tally.tally_seq,
          tally_type: props.tally?.tally_type,
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


      const partCert = props.tally?.part_cert;

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

            <Text style={styles.bottomSheetTitle}>{
          partCert?.type === 'o'
            ? `${partCert?.name}`
            : `${partCert?.name?.first}${partCert?.name?.middle ? ' ' + partCert?.name?.middle + ' ' : ''} ${partCert?.name?.surname}`
        }</Text>
        <Text style={[styles.bottomSheetSub, { marginTop: 4 }]}>{partCert?.chad?.cid}:{formatRandomString(partCert?.chad?.agent)}</Text>
          </View>

          <View style={{ flex: 1 }} />
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
    backgroundColor: "white",
    borderColor: "blue",
    width: "100%",
    borderRadius: 40,
    height: 45,
    alignItems: "center",
    justifyContent: "center",
    marginBottom: 20,
  },

  button: {
    backgroundColor: "blue",
    borderColor: "blue",
    width: "100%",
    borderRadius: 40,
    height: 45,
    marginBottom: 20,
    alignItems: "center",
    justifyContent: "center",
  },
  close: {
    alignSelf: "flex-end",
    backgroundColor: "white",
    height: 24,
    width: 24,
    justifyContent: "center",
    alignItems: "center",
  },
});

export default PayModal;

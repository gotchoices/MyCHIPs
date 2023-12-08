import React, { useState } from "react";
import { View, Text, StyleSheet, Alert } from "react-native";
import stringify from 'json-stable-stringify';

import { useSelector } from "react-redux";
import Avatar from "../../../components/Avatar";
import Button from "../../../components/Button";
import useSocket from "../../../hooks/useSocket";
import { colors } from "../../../config/constants";
import TallyEntryModal from "../../Invite/TallyEntryModal";
import SuccessContent from "../../../components/SuccessContent";
import { acceptTally, offerTally } from "../../../services/tally";
import { createSignature } from "../../../utils/message-signature";
import BottomSheetModal from "../../../components/BottomSheetModal";

const NavigationTallyRequest = (props) => {
  const { tally } = props;
  const { wm } = useSocket();

  const [offering, setOffering] = useState(false);
  const [accepting, setAccepting] = useState(false);
  const { imagesByDigest } = useSelector((state) => state.avatar);
  const [showAcceptSuccess, setShowAcceptSuccess] = useState(false);

  const [negotiationData, setNegotiationData] = useState({
    showModal: false,
    data: undefined,
  });

  const [showOfferSuccess, setShowOfferSuccess] = useState({
    show: false,
    offerTo: "",
    tally_ent: null,
    tally_seq: null,
  });

  const partCert = tally.part_cert;
  const avatar = imagesByDigest[digest];
  const digest = partCert?.file?.[0]?.digest;

  const state = tally.state;
  const canShare = state === "draft";
  const canOffer = state === "P.draft";
  const canAccept = state === "P.offer";

  const first = tally.part_cert?.name?.first;
  const middle = tally.part_cert?.name?.middle;
  const surname = tally.part_cert?.name?.surname;
  const name =
    tally.part_cert?.type === "o"
      ? `${tally.part_cert?.name}`
      : `${first}${middle ? " " + middle : ""}${surname ? " " + surname : ""}`;
  const limit = tally.part_terms?.limit ?? 0;
  const holdDigest = tally.hold_cert?.file?.[0]?.digest;
  const partDigest = tally.part_cert?.file?.[0]?.digest;
  const tally_uuid = tally.tally_uuid;

  const onNegotiationModalClose = () => {
    setNegotiationData({
      showModal: false,
      data: undefined,
    });
  };

  const resetNegotiationData = () => {
    setNegotiationData({
      showModal: false,
      data: undefined,
    });
  };

  const onDismissOfferSuccess = () => {
    setShowOfferSuccess({
      show: false,
      offerTo: "",
      tally_ent: null,
      tally_seq: null,
    });
  };

  const onDoneOfferSuccess = () => {
    const tally_ent = showOfferSuccess?.tally_ent;
    const tally_seq = showOfferSuccess?.tally_seq;

    onDismissOfferSuccess();

    if (tally_ent && tally_seq) {
      props.navigation.navigate("TallyPreview", {
        tally_seq,
        tally_ent,
      });
    }
  };

  const onAccept = async ({ tally_ent, tally_seq, json }) => {
    setAccepting(true);

    const _json = stringify(json);
    createSignature(_json)
      .then((signature) => {
        return acceptTally(wm, { tally_ent, tally_seq, signature });
      })
      .then((result) => {
        setShowAcceptSuccess(true);
        resetNegotiationData();
      })
      .catch((err) => {
        const { isKeyAvailable, message } = err;
        if (isKeyAvailable === false) {
          Alert.alert(
            "Create Keys",
            "Seems like there is no key to create signature please continue to create one and accept tally.",
            [{ text: "Cancel" }, { text: "Continue", onPress: showGenerateKey }]
          );
        } else {
          Alert.alert("Error", message || err);
        }
      })
      .finally(() => {
        setAccepting(false);
      });
  };

  const onOffer = async ({ tally_uuid, tally_ent, tally_seq, name, json }) => {
    setOffering(true);
    
    const _json = stringify(json);
    createSignature(_json)
      .then((signature) => {
        return offerTally(wm, {
          tally_uuid,
          tally_ent,
          tally_seq,
          signature,
        });
      })
      .then((result) => {
        resetNegotiationData();

        setShowOfferSuccess({
          show: true,
          offerTo: name,
          tally_ent,
          tally_seq,
        });

      })
      .catch((err) => {
        const { isKeyAvailable, message } = err;
        if (isKeyAvailable === false) {
          Alert.alert(
            "Create Keys",
            "Seems like there is no key to create signature please continue to create one and accept tally.",
            [{ text: "Cancel" }, { text: "Continue", onPress: showGenerateKey }]
          );
        } else {
          Alert.alert("Error", message || err);
        }
      })
      .finally(() => {
        setOffering(false);
      });
  };

  const onReview = (tally_seq, tally_ent) => {
    props.navigation.navigate("TallyPreview", {
      tally_seq,
      tally_ent,
    });

    resetNegotiationData();
  };

  const onTallyOpenDone = () => {
    props.navigation.navigate("Home");
  };

  const onAcceptPressed = () => {
    if (canOffer || canAccept) {
      setNegotiationData({
        showModal: true,
        data: {
          name,
          limit,
          canShare,
          canOffer,
          canAccept,
          partDigest,
          holdDigest,
          tally_uuid,
          json: tally.json,
          tally_seq: tally.tally_seq,
          tallyType: tally.tally_type,
          tally_ent: tally.tally_ent,
        },
      });
      return;
    }

    props.navigation.navigate("TallyPreview", {
      tally_seq: tally.tally_seq,
      tally_ent: tally.tally_ent,
    });
  };

  const ActionView = () => {
    return (
      <View style={styles.price}>
        <Text style={[styles.description, { marginBottom: 5 }]}>45 min</Text>

        <View style={styles.buttonView}>
          <Button
            title="Review"
            textColor="blue"
            textStyle={styles.text}
            style={styles.secondaryButton}
            onPress={() => onReview(tally.tally_seq, tally.tally_ent)}
          />

          <Button
            title="Accept"
            style={styles.button}
            textStyle={styles.text}
            onPress={onAcceptPressed}
          />
        </View>
      </View>
    );
  };

  return (
    <>
      <View style={styles.container}>
        <Avatar style={styles.avatar} avatar={avatar} />

        <View style={{ flex: 1 }}>
          <Text style={styles.name}>{name}</Text>
          <Text style={[styles.description, { marginTop: 4 }]}>
            Tally Request
          </Text>
        </View>

        <ActionView />
      </View>

      <BottomSheetModal
        isVisible={negotiationData.showModal}
        onClose={onNegotiationModalClose}
      >
        <TallyEntryModal
          onOffer={onOffer}
          onReview={onReview}
          onAccept={onAccept}
          offering={offering}
          accepting={accepting}
          negotiationData={negotiationData}
          onNeogitationModalClose={onNegotiationModalClose}
        />
      </BottomSheetModal>

      <BottomSheetModal
        isVisible={showOfferSuccess.show}
        onClose={onDismissOfferSuccess}
      >
        <SuccessContent
          buttonTitle="View"
          onDone={onDoneOfferSuccess}
          onDismiss={onDismissOfferSuccess}
          message={`Sending tally offer to ${showOfferSuccess.offerTo}`}
        />
      </BottomSheetModal>

      <BottomSheetModal
        isVisible={showAcceptSuccess}
        onClose={() => setShowAcceptSuccess(false)}
      >
        <SuccessContent
          buttonTitle="View"
          onDone={onTallyOpenDone}
          message="Your tally is now open"
          onDismiss={() => setShowAcceptSuccess(false)}
        />
      </BottomSheetModal>
    </>
  );
};

const myChipsNet = {
  fontSize: 18,
  paddingBottom: 3,
  fontWeight: "600",
  color: colors.green,
};

const styles = StyleSheet.create({
  button: {
    width: 50,
    height: 25,
    marginBottom: 3,
    borderRadius: 40,
    paddingVertical: 0,
    borderColor: "blue",
    alignItems: "center",
    backgroundColor: "blue",
    justifyContent: "center",
  },
  secondaryButton: {
    height: 23,
    width: 50,
    marginBottom: 3,
    borderRadius: 40,
    paddingVertical: 0,
    borderColor: "blue",
    alignItems: "center",
    backgroundColor: "white",
    justifyContent: "center",
    marginRight: 10,
  },
  container: {
    height: 50,
    flexDirection: "row",
    alignItems: "center",
    justifyContent: "space-between",
  },
  profile: {
    flexDirection: "row",
  },
  avatar: {
    marginRight: 8,
    alignSelf: "center",
    height: 55,
    width: 55,
    borderRadius: 55 / 2,
  },
  name: {
    fontSize: 16,
    fontWeight: "bold",
  },
  description: {
    fontSize: 12,
    color: colors.gray500,
  },
  price: {
    alignItems: "flex-end",
  },
  myChips: {
    flexDirection: "row",
    alignItems: "center",
  },
  myChipsNet,
  myChipsNetNeg: {
    ...myChipsNet,
    color: colors.red,
  },
  dollar: {
    color: colors.green,
    fontSize: 10,
    fontWeight: "600",
  },
  dollarNeg: {
    color: colors.red,
    fontSize: 10,
    fontWeight: "600",
  },
  buttonView: {
    marginRight: -10,
    flexDirection: "row",
    alignItems: "center",
  },
  text: {
    fontSize: 10,
  },
});

export default NavigationTallyRequest;

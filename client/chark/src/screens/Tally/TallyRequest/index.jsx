import { StyleSheet, View, Text, Dimensions } from "react-native";
import React, { useEffect, useState } from "react";

import Button from "../../../components/Button";
import Avatar from "../../../components/Avatar";
import { colors } from "../../../config/constants";
import useSocket from "../../../hooks/useSocket";
import { useTallyText } from "../../../hooks/useLanguage";
import { fetchTallies } from "../../../services/tally";
import { useSelector } from "react-redux";
import { formatRandomString } from "../../../utils/format-string";
import CustomIcon from "../../../components/CustomIcon";

const TallyRequest = (props) => {
  const { tally_seq, tally_ent } = props;
  const { wm } = useSocket();
  const tallyText = useTallyText(wm);

  const [tally, setTally] = useState();
  const [target, setTarget] = useState("");
  const [bound, setBound] = useState("");
  const [reward, setReward] = useState("");
  const [clutch, setClutch] = useState("");

  const [contractName, setContractName] = useState("");

  const {
    imageFetchTrigger,
    tallies: tallies,
    imagesByDigest,
    fetching,
  } = useSelector((state) => state.openTallies);

  useEffect(() => {
    fetchTally();
  }, [tally_seq, tally_ent]);

  const fetchTally = () => {
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
        "hold_cert",
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

  const onViewPartnerCertificate = () => {};

  const onChoose = () => {};

  const partCert = tally?.part_cert;

  return (
    <View style={styles.main}>
      <CustomIcon
        name="close"
        size={16}
        onPress={props.onClose}
        style={styles.close}
      />
      <View style={styles.center}>
        <Avatar
          style={styles.profileImage}
          avatar={imagesByDigest?.[tally?.part_cert?.file?.[0]?.digest]}
        />

        <Text style={[styles.topSub, { marginTop: 4 }]}>
          {partCert?.chad?.cid}:{formatRandomString(partCert?.chad?.agent)}
        </Text>

        <Text style={styles.bottomSheetTitle}>
          {partCert?.type === "o"
            ? `${partCert?.name}`
            : `${partCert?.name?.first}${
                partCert?.name?.middle ? " " + partCert?.name?.middle + " " : ""
              } ${partCert?.name?.surname}`}
        </Text>

        <Text style={[styles.bottomSheetSub, { marginTop: 4 }]}>
          Wants to start a Tally with you
        </Text>
      </View>

      <Button
        textColor="blue"
        title="View Partner Certificate"
        onPress={onViewPartnerCertificate}
        style={styles.secondaryButton}
      />

      <Button
        title="Choose Certificate"
        onPress={onChoose}
        style={styles.button}
      />
    </View>
  );
};

const styles = StyleSheet.create({
  main: { paddingHorizontal: 20, flex: 2, backgroundColor: "white" },
  center: {
    flex: 1,
    alignItems: "center",
    justifyContent: "center",
  },
  close: {
    position: "absolute",
    top: 80,
    left: 30,
    height: 24,
    width: 24,
    justifyContent: "center",
    alignItems: "center",
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
  bottomSheetTitle: {
    fontSize: 24,
    fontWeight: "500",
    fontFamily: "inter",
    color: colors.black,
  },
  bottomSheetSub: {
    fontSize: 18,
    fontWeight: "500",
    color: "#636363",
    fontFamily: "inter",
    paddingBottom: 30,
  },
  topSub: {
    fontSize: 14,
    color: "#636363",
    fontFamily: "inter",
    paddingBottom: 30,
  },
});

export default TallyRequest;

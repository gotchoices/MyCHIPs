import {
  View,
  Text,
  TextInput,
  ScrollView,
  StyleSheet,
  RefreshControl,
} from "react-native";
import React, { useEffect, useState } from "react";

import {
  fetchTallies,
  fetchContracts,
  fetchTradingVariables,
} from "../../../services/tally";
import useSocket from "../../../hooks/useSocket";
import { colors } from "../../../config/constants";
import { useHoldTermsText, useTallyText } from "../../../hooks/useLanguage";

import Button from "../../../components/Button";
import CommonTallyView from "../CommonTallyView";
import HelpText from "../../../components/HelpText";
import CustomText from "../../../components/CustomText";
import useMessageText from "../../../hooks/useMessageText";

const EditOpenTally = (props) => {
  const { tally_seq, tally_ent } = props.route?.params ?? {};
  const { wm } = useSocket();
  const tallyText = useTallyText(wm);

  const [loading, setLoading] = useState(true);
  const [tally, setTally] = useState();
  const [target, setTarget] = useState("");
  const [bound, setBound] = useState("");
  const [reward, setReward] = useState("");
  const [clutch, setClutch] = useState("");

  const [contractName, setContractName] = useState("");

  useHoldTermsText(wm);
  const { messageText } = useMessageText();
  const holdTermsText = messageText?.terms_lang?.hold_terms?.values;
  const partTermsText = messageText?.terms_lang?.part_terms?.values;
  const hasPartCert = !!tally?.part_cert;
  const hasHoldCert = !!tally?.hold_cert;

  // fields: ['tally_uuid', 'tally_date', 'status', 'target', 'bound', 'reward', 'clutch', 'part_cert'],
  useEffect(() => {
    fetchTally();
  }, [tally_seq, tally_ent]);

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
        'hold_chad',
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

  const showTradingVariables = () => {
    props.navigation.navigate("TradingVariables", {
      tally_seq,
      tally_ent,
      tally_type: tally?.tally_type,
      chad: tally?.hold_chad,
      tally_uuid: tally?.tally_uuid,
    });
  };

  const onSave = () => {
    const data = {
      target: parseInt(target),
      bound: parseInt(bound),
      reward: parseFloat(reward),
      clutch: parseFloat(clutch),
    };

    console.log(data, "data");
  };

  useEffect(() => {
    if (tally?.contract) {
      fetchContracts(wm, {
        fields: ["name", "language", "rid", "host"],
        where: { rid: tally.contract },
      }).then((data) => {
        setContractDetails(data);
      });
    }
  }, [tally?.contract]);

  const setContractDetails = (data) => {
    try {
      const name = JSON.parse(data);

      setContractName(name);
    } catch (e) {
      setContractName(data?.[0]?.name);
    }
  };

  if (loading) {
    return (
      <View style={{ flex: 1, alignItems: "center", justifyContent: "center" }}>
        <Text>Loading...</Text>
      </View>
    );
  }

  if (!tally) {
    return (
      <View style={{ flex: 1, alignItems: "center" }}>
        <CustomText as="h2">Tally not found</CustomText>
      </View>
    );
  }

  const onViewChitHistory = () => {
    const partCert = tally?.part_cert;
    console.log("DIGEST_HAVE ==> ", JSON.stringify(partCert));
    props.navigation.navigate("ChitHistory", {
      tally_seq: tally?.tally_seq,
      tally_ent,
      tally_uuid: tally?.tally_uuid,
      part_name: `${partCert?.name?.first}${partCert?.name?.middle ? " " + partCert?.name?.middle + " " : ""
        } ${partCert?.name?.surname}`,
      digest: partCert?.file?.[0]?.digest,
      date: tally?.tally_date,
      net: tally?.net,
      cid: partCert?.chad?.cid,
    });
  };

  const onPay = () => {
    props.navigation.navigate("PaymentDetail", {
      tally_uuid: tally?.tally_uuid,
      chit_seq: tally?.tally_seq,
      tally_type: tally?.tally_type,
    });
  };

  const onRequest = () => {
    props.navigation.navigate("RequestDetail", {
      tally_uuid: tally?.tally_uuid,
      chit_seq: tally?.tally_seq,
      tally_type: tally?.tally_type,
    });
  };

  const showPDF = () => {
    props.navigation.navigate("InviteScreen", {
      screen: "TallyContract",
      initial: false,
      params: {
        tally_seq,
      },
    });
  }

  const onViewCertificate = (data) => {
    props.navigation.navigate("TallyCertificate", {
      title: '',
      tally_ent,
      tally_seq,
      cert: data
    });
  }

  return (
    <ScrollView
      refreshControl={
        <RefreshControl refreshing={loading} onRefresh={fetchTally} />
      }
    >
      <View>
        <View style={styles.container}>
          <CommonTallyView
            tally={tally}
            onViewChitHistory={onViewChitHistory}
            onPay={onPay}
            onRequest={onRequest}
            onPartnerCertificate={()=>onViewCertificate({ title: "Partner Certificate", data: tally?.part_cert })}
          />

          <View style={styles.detailControl}>
            <CustomText as="h5">Tally Type</CustomText>
            <Text style={styles.textInputStyle}>{tally.tally_type}</Text>
          </View>

          <View style={styles.detailControl}>
            <HelpText
              label={tallyText?.contract?.title ?? ""}
              helpText={tallyText?.contract?.help}
              style={styles.h5}
            />

            {contractName && <Text>{contractName}</Text>}
          </View>

          <Button
            title="Show PDF"
            textColor={colors.blue}
            style={styles.showPDF}
            onPress={showPDF}
          />

          {/* {
            hasPartCert ? <Button
              title="View Partner Certificate"
              onPress={() => onViewCertificate({ title: "Partner Certificate", data: tally?.part_cert })}
              textColor={colors.blue}
              style={styles.showPDF}
            /> : <></>
          } */}

          {
            hasHoldCert ? <Button
              title="View Holder Certificate"
              onPress={() => onViewCertificate({ title: "Holder Certificate", data: tally?.hold_cert })}
              textColor={colors.blue}
              style={styles.showPDF}
            /> : <></>
          }
        </View>
      </View>

      <View style={styles.container}>
          <HelpText
            label={tallyText?.hold_terms?.title ?? ""}
            helpText={tallyText?.hold_terms?.help}
            style={styles.label}
          />
          {holdTermsText?.map((holdTerm, index) => {
            return (
              <View
                key={`${holdTerm?.value}${index}`}
              >
                <HelpText
                  label={holdTerm?.title ?? ""}
                  helpText={holdTerm?.help}
                  style={styles.label}
                />

                <Text style={styles.textInputStyle}>
                  {tally.hold_terms?.[holdTerm?.value] ?? 0}
                </Text>
              </View>
            );
          })}

      </View>

      <View style={styles.container}>
          <HelpText
            label={tallyText?.part_terms?.title ?? ""}
            helpText={tallyText?.part_terms?.help}
            style={styles.label}
          />
          {partTermsText?.map((partTerm, index) => {
            return (
              <View
                key={`${partTerm?.value}${index}`}
              >
                <HelpText
                  label={partTerm?.title ?? ""}
                  helpText={partTerm?.help}
                  style={styles.h5}
                />

                <Text style={styles.textInputStyle}>
                  {tally.part_terms?.[partTerm?.value] ?? 0}
                </Text>
              </View>
            );
          })}
   
      </View>

      <View style={styles.container}>
        <HelpText label={"Trading Variables"} style={styles.label} />

        <Button
          title="Show Trade"
          style={{ borderRadius: 12, width: 120, marginTop: 12 }}
          onPress={showTradingVariables}
        />
      </View>
    </ScrollView >
  );
};

const styles = StyleSheet.create({
  container: {
    margin: 10,
    padding: 10,
    marginVertical:5,
    backgroundColor: colors.white,
  },
  detailControl: {
    marginVertical: 10,
  },
  input: {
    paddingHorizontal: 10,
    paddingVertical: 10,
    backgroundColor: colors.gray100,
  },
  comment: {
    textAlignVertical: "top",
  },
  textInputStyle: {
    marginTop:5,
    fontSize: 12,
    color: "black",
    paddingVertical: 16,
    paddingHorizontal: 10,
    backgroundColor: colors.gray100,
  },
  label: {
    fontWeight: "500",
    fontSize: 13,
    marginBottom: 0,
    color: colors.black,
  },
  headerText: {
    fontSize: 14,
    color: 'black',
  },
  showPDF: {
    marginTop: 12,
    backgroundColor: colors.white
  ,
  h5: {
    fontSize: 12,
    marginBottom: 0,
    fontWeight: "500",
    color: colors.gray300,
  },}

})

export default EditOpenTally;

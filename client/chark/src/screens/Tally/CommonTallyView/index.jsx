import React, { useState, useEffect, useMemo } from "react";
import {
  View,
  Text,
  Linking,
  StyleSheet,
  TouchableOpacity,
} from "react-native";
import HelpText from "../../../components/HelpText";
import {
  colors,
  connectsObj,
  dateFormats,
} from "../../../config/constants";
import useMessageText from "../../../hooks/useMessageText";

import Button from "../../../components/Button";
import { round } from "../../../utils/common";
import { ChitIcon } from "../../../components/SvgAssets/SvgAssets";
import { formatDate } from "../../../utils/format-date";

import { fetchTallyFile } from "../../../services/tally";
import useSocket from "../../../hooks/useSocket";
import { Buffer } from "buffer";
import TallyReviewView from "../../TallyReview/TallyReviewView";
import CertificateInformation from '../CertificateInformation';

const CommonTallyView = (props) => {
  const tally = props.tally;
  const { messageText } = useMessageText();
  const userTallyText = messageText?.tallies_v_me?.col;
  const [avatar, setAvatar] = useState(undefined);
  const { wm } = useSocket();

  const net = round((tally?.net ?? 0) / 1000, 3);
  const talliesText = messageText?.tallies;
  const hasPartCert = !!tally?.part_cert;
  const hasHoldCert = !!tally?.hold_cert;
  const hasNet = !!tally?.net;
  const isNetNegative = tally?.net < 0;

  const connects = tally?.part_cert?.connect;
  const partCert = tally?.part_cert;

  const partName= Object.values((tally.part_cert?.name ?? {})).join(' ')
  const partChipAddress = hasPartCert ? `${tally.part_cert?.chad?.cid ?? ''}-${tally.part_cert?.chad?.agent ?? ''}` : '';
  const partEmail = useMemo(() => {
    if(hasPartCert) {
      const found = (tally.part_cert?.connect ?? []).find(connect => connect.media === 'email')
      return found?.address ?? ''
    }

    return '';
  }, [hasPartCert, tally.part_cert?.connect])

  const holdName= Object.values((tally.hold_cert ?.name ?? {})).join(' ')
  const holdChipAddress = hasHoldCert ? `${tally.hold_cert?.chad?.cid ?? ''}-${tally.hold_cert?.chad?.agent ?? ''}` : '';
  const holdEmail = useMemo(() => {
    if(hasHoldCert) {
      const found = (tally.hold_cert?.connect ?? []).find(connect => connect.media === 'email')
      return found?.address ?? ''
    }

    return '';
  }, [hasHoldCert, tally.hold_cert?.connect])

  useEffect(() => {
    const digest = tally?.part_cert?.file?.[0]?.digest;
    const tally_seq = tally?.tally_seq;

    if (digest && wm) {
      fetchTallyFile(wm, digest, tally_seq)
        .then((data) => {
          console.log("TALLY_SEQ ==> ", JSON.stringify(data));
          const fileData = data?.[0]?.file_data;
          const file_fmt = data?.[0]?.file_fmt;
          if (fileData) {
            const base64 = Buffer.from(fileData).toString("base64");
            setAvatar(`data:${file_fmt};base64,${base64}`);
          }
        })
        .catch((err) => {
          console.log("TALLY_FILE_ERROR ==> ", err);
        });
    }
  }, [wm, tally]);

  const handleLinkPress = (link) => {
    Linking.canOpenURL(link)
      .then((supported) => {
        if (supported) {
          Linking.openURL(link);
        } else {
          console.log("Cannot open URL: ", link);
        }
      })
      .catch((error) => console.log("Error occurred:", error));
  };

  const onViewCertificate= (args) => {
    return () => props.navigation.navigate("TallyCertificate", { 
      title: args.title,
      cert: args.cert,
      state: tally.state,
      tally_seq: tally.tally_seq,
      tally_ent: tally.tally_ent,
    });
  }

  return (
    <View>
      {hasNet && (
        <View style={styles.detailControl}>
          <HelpText label={"tally_balance_text"} style={styles.heading} />
          <View>
            <View style={styles.row}>
              <ChitIcon
                color={isNetNegative ? colors.red : colors.green}
                height={14}
                width={14}
              />
              <Text
                style={
                  isNetNegative
                    ? styles.negativeText
                    : styles.positiveText
                }
              >
                {net}
              </Text>
            </View>

            <View style={{ marginTop: 20, marginBottom: 30 }}>
              <TallyReviewView
                net={tally?.net}
                tallyType={tally?.tally_type}
                partTerms={tally?.part_terms}
                holdTerms={tally?.hold_terms}
                partCert={tally?.part_cert ?? {}}
                holdCert={tally?.hold_cert ?? {}}
                onHoldTermsChange={() => {}}
                onPartTermsChange={() => {}}
                canEdit={true}
              />
            </View>

            <View style={{ flexDirection: "row", marginTop: 12 }}>
              <Button
                title="chit_history_text"
                onPress={props.onViewChitHistory}
                style={{ borderRadius: 12, width: 120 }}
              />

              <Button
                title="pay_text"
                onPress={props.onPay}
                style={{
                  borderRadius: 12,
                  paddingHorizontal: 22,
                  marginStart: 12,
                }}
              />

              <Button
                title={userTallyText?.request?.title ?? ''}
                onPress={props.onRequest}
                style={{
                  borderRadius: 12,
                  paddingHorizontal: 22,
                  marginStart: 12,
                }}
              />
            </View>
          </View>
        </View>
      )}

      {hasPartCert && (
        <CertificateInformation
          title={userTallyText?.part_cert?.title ?? ''}
          name={partName}
          chipAddress={partChipAddress}
          email={partEmail}
          onViewDetails={onViewCertificate({ title: 'Partner Certificate', cert: tally?.part_cert ?? {} })}
          certText={userTallyText?.part_cert ?? {}}
        />
      )}

      {!!tally?.hold_cert && (
        <CertificateInformation
          title={userTallyText?.hold_cert?.title ?? ''}
          name={holdName}
          chipAddress={holdChipAddress}
          email={holdEmail}
          onViewDetails={onViewCertificate({ title: 'My Certificate', cert: tally?.hold_cert ?? {} } )}
          certText={userTallyText?.hold_cert ?? {}}
        />
      )}

      <View style={styles.detailControl}>
        <HelpText
          label={talliesText?.tally_uuid?.title ?? ""}
          helpText={talliesText?.tally_uuid?.help}
          style={styles.heading}
        />
        <Text>{tally?.tally_uuid}</Text>
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={talliesText?.tally_date?.title ?? ""}
          helpText={talliesText?.tally_date?.help}
          style={styles.heading}
        />
        <Text>
          {/* {new Date(tally.tally_date).toLocaleString()} */}
          {formatDate({
            date: tally?.tally_date,
            format: dateFormats.dateTime,
          })}
        </Text>
      </View>

      <View style={styles.detailControl}>
        <HelpText
          label={talliesText?.status?.title ?? ""}
          helpText={talliesText?.status?.help}
          style={styles.heading}
        />

        <Text>{tally?.status}</Text>
      </View>
    </View>
  );
};

const styles = StyleSheet.create({
  detailControl: {
    marginVertical: 10,
  },
  headerText: {
    color: colors.black,
    fontSize: 14,
  },
  secondaryheader: {
    color: colors.black,
    fontSize: 13,
    fontWeight: "normal",
  },
  label: {
    fontWeight: "bold",
    color: colors.black,
    fontSize: 14,
  },
  image: {
    height: 14,
    width: 14,
  },
  positiveText: {
    color: "green",
  },
  negativeText: {
    color: "red",
  },
  row: {
    flexDirection: "row",
    alignItems: "center",
  },
  heading: {
    fontWeight: "500",
    fontSize: 12,
    marginBottom: 0,
    color: colors.gray300,
  },
  certInfoWrapper: {
    backgroundColor: colors.gray5,
    borderWidth: 1,
    borderColor: colors.gray7,
    borderRadius: 8,
    padding: 16,
  },
  certInfo: {
    marginBottom: 12,
    fontFamily: "inter",
  },
  certValue: {
    color: colors.black,
    fontSize: 12,
    fontWeight: "500",
    fontFamily: "inter",
  },
  certInfoLabel: {
    fontWeight: "500",
    fontSize: 11,
    marginBottom: 0,
    color: colors.gray300,
  },
  certOtherDetails: {
    color: colors.blue3,
    textDecorationLine: "underline",
  },
});

export default CommonTallyView;

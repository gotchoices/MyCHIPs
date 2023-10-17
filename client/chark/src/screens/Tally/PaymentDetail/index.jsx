import React, { useEffect, useMemo, useRef, useState } from "react";
import {
  StyleSheet,
  ScrollView,
  View,
  TextInput,
  ActivityIndicator,
  Text,
  Alert,
  TouchableOpacity,
} from "react-native";
import { useSelector } from "react-redux";

import { colors } from "../../../config/constants";
import Button from "../../../components/Button";
import useProfile from "../../../hooks/useProfile";
import { getCurrency } from "../../../services/user";
import useSocket from "../../../hooks/useSocket";
import { round } from "../../../utils/common";
import { insertChit } from "../../../services/tally";
import { useTallyLanguage } from "../../../hooks/useLanguage";
import useMessageText from "../../../hooks/useMessageText";
import HelpText from "../../../components/HelpText";

import { ChitIcon, SwapIcon } from "../../../components/SvgAssets/SvgAssets";
import BottomSheetModal from "../../../components/BottomSheetModal";
import SuccessModal from "../Success";

const PaymentDetail = (props) => {
  const { tally_uuid, chit_seq, tally_type } = props.route?.params;
  const { wm } = useSocket();
  const { preferredCurrency } = useSelector((state) => state.profile);
  const [conversionRate, setConversionRate] = useState(undefined);
  const currencyCode = preferredCurrency.code;

  const [memo, setMemo] = useState();
  const [reference, setReference] = useState();
  const [chit, setChit] = useState();

  const [usd, setUSD] = useState();

  const [loading, setLoading] = useState(false);
  const [disabled, setDisabled] = useState(false);

  const [isSwitched, setIsSwitched] = useState(false);

  const [showSuccess, setShowSuccess] = useState(false);

  const ref = useRef("");

  useTallyLanguage(wm);
  const { messageText } = useMessageText();

  const referenceText = messageText?.chits_lang?.reference;
  const memoText = messageText?.chits_lang?.memo;
  const netText = messageText?.chits_lang?.net;

  useEffect(() => {
    if (currencyCode) {
      setLoading(true);
      getCurrency(wm, currencyCode)
        .then((data) => {
          setConversionRate(parseFloat(data?.rate ?? 0));
        })
        .catch((err) => {
          console.log("EXCEPTION ==> ", err);
        })
        .finally(() => {
          setLoading(false);
        });
    }
  }, [currencyCode]);

  const totalNetDollar = (text) => {
    const convertedChit = parseInt(text);
    if (conversionRate && convertedChit) {
      const total = convertedChit * conversionRate;
      const totalValue = round(total, 2);

      return setUSD(totalValue);
    }

    setUSD(0);
  };

  const totalChit = (text) => {
    const convertedUSD = parseInt(text);
    if (conversionRate && convertedUSD) {
      const total = convertedUSD / conversionRate;
      const totalValue = round(total, 2);

      return setChit(totalValue);
    }

    setChit(0);
  };

  const onMakePayment = () => {
    const net = round((chit ?? 0) * 1000, 0);

    if (net < 0) {
      Alert.alert("Alert", "Can't input negative chit.");
      return;
    }
    setDisabled(true);
    const payload = {
      reference: JSON.stringify(reference),
      memo: memo,
      status: "open",
      signature: "Signature",
      issuer: tally_type,
      request: "good",
      units: net,
      tally_uuid,
      chit_seq,
    };
    console.log("LOG_DATA ==> ", JSON.stringify(payload));

    insertChit(wm, payload)
      .then((result) => {
        console.log("RESULT ==> ", result);
        setShowSuccess(true);
      })
      .catch((err) => {
        console.log("ERROR ==> ", err);
        Alert.alert("Error", JSON.stringify(err));
      })
      .finally(() => {
        setDisabled(false);
      });
  };

  if (loading) {
    return (
      <View style={{ flex: 1, justifyContent: "center", alignItems: "center" }}>
        <ActivityIndicator size={"large"} />
      </View>
    );
  }

  return (
    <ScrollView
      style={styles.container}
      contentContainerStyle={styles.contentContainer}
    >
      <View style={styles.centerWrapper}>
        {isSwitched ? (
          <>
            <View style={styles.row}>
              <Text style={styles.text}>USD</Text>
              <TextInput
                style={styles.amount}
                placeholder="0.00"
                keyboardType="number-pad"
                value={usd}
                onChangeText={(text) => {
                  setUSD(text);
                  totalChit(text);
                }}
              />
            </View>

            {currencyCode && chit ? (
        <View style={[styles.row,{alignSelf:'flex-end',marginRight:20}]}>
                <ChitIcon color={colors.black} height={18} width={12} />
                <Text style={[styles.text,{marginLeft:10}]}>{chit}</Text>
              </View>
            ) : (
              <></>
            )}
          </>
        ) : (
          <>
            <View style={styles.row}>
              <ChitIcon color={colors.black} height={18} width={12} />
              <TextInput
                style={styles.amount}
                placeholder="0.00"
                keyboardType="number-pad"
                value={chit}
                onChangeText={(text) => {
                  setChit(text);
                  totalNetDollar(text);
                }}
              />
            </View>

            {currencyCode && usd ? (
            <View style={[styles.row,{alignSelf:'flex-end',marginRight:20}]}>
                <Text style={styles.text}>
                  {usd} {currencyCode}
                </Text>
              </View>
            ) : (
              <></>
            )}
          </>
        )}
      </View>

      {currencyCode ? (
        <TouchableOpacity
          style={styles.icon}
          onPress={() => setIsSwitched(!isSwitched)}
        >
          <SwapIcon />
        </TouchableOpacity>
      ) : (
        <></>
      )}

      <TouchableOpacity
        style={styles.input}
        onPress={() => ref.current.focus()}
      >
        <TextInput
          ref={ref}
          placeholder="Message"
          value={reference}
          onChangeText={setReference}
        />
      </TouchableOpacity>

      <View style={styles.buttonView}>
        <Button
          style={styles.button}
          title="Pay"
          onPress={onMakePayment}
          disabled={disabled}
        />
      </View>

      <BottomSheetModal
        isVisible={showSuccess}
        onClose={() => setShowSuccess(false)}
      >
        <SuccessModal
          onClose={() => {
            props.navigation.goBack();

            setShowSuccess(false);
          }}
        />
      </BottomSheetModal>
    </ScrollView>
  );
};

const styles = StyleSheet.create({
  container: {
    flex: 1,
    paddingVertical: 50,
    backgroundColor: colors.white,
  },
  amount: {
    paddingLeft: 10,
    fontSize: 26,
    paddingVertical: 20,
    fontWeight: "500",
    fontFamily: "inter",
    color: colors.black,
  },
  contentContainer: {
    flex: 1,
    padding: 16,
    backgroundColor: "white",
  },
  input: {
    height: 100,
    padding: 10,
    borderRadius: 4,
    marginBottom: 16,
    borderWidth: 0.2,
    borderColor: colors.gray300,
  },
  headerText: {
    color: colors.black,
    fontSize: 14,
  },
  button: {
    height: 45,
    width: "100%",
    borderRadius: 40,
    marginBottom: 20,
    borderColor: "blue",
    alignItems: "center",
    justifyContent: "center",
    backgroundColor: "blue",
  },
  centerWrapper: {
    marginBottom: 30,
    alignItems: "center",
    justifyContent: "center",
  },
  buttonView: {
    flex: 1,
    justifyContent: "flex-end",
  },
  row: {
    width:200,
    paddingRight:20,
    flexDirection: "row",
    alignItems: "center",
    justifyContent:'center'
  },
  text: {
    fontWeight: "500",
    color: colors.gray300,
  },
  icon: {
    position: "absolute",
    right: 60,
    top: 40,
  },
});

export default PaymentDetail;

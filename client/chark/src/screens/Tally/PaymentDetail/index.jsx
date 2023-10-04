import React, { useEffect, useMemo, useState } from "react";
import { StyleSheet, ScrollView, View, TextInput, ActivityIndicator, Text, Alert } from "react-native"
import { useSelector } from 'react-redux';

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

const PaymentDetail = (props) => {
  const { tally_uuid, chit_seq, tally_type } = props.route?.params;
  const { wm } = useSocket();
  const { preferredCurrency } = useSelector(state => state.profile);
  const [conversionRate, setConversionRate] = useState(undefined);
  const currencyCode = preferredCurrency.code;

  const [memo, setMemo] = useState();
  const [reference, setReference] = useState();
  const [chit, setChit] = useState();

  const [loading, setLoading] = useState(false);
  const [disabled, setDisabled] = useState(false);
  
  useTallyLanguage(wm);
  const { messageText } = useMessageText();

  const referenceText = messageText?.chits_lang?.reference;
  const memoText = messageText?.chits_lang?.memo;
  const netText = messageText?.chits_lang?.net;

  useEffect(() => {
    if (currencyCode) {
      setLoading(true);
      getCurrency(wm, currencyCode).then(data => {
        setConversionRate(parseFloat(data?.rate ?? 0));
      }).catch(err => {
        console.log("EXCEPTION ==> ", err);
      }).finally(() => {
        setLoading(false);
      })
    }
  }, [currencyCode])

  const totalNetDollar = useMemo(() => {
    const convertedChit = parseInt(chit);
    if (conversionRate && convertedChit) {
      const total = convertedChit * conversionRate;
      return round(total, 2);
    }

    return 0;
  }, [chit, conversionRate])

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
      status: 'open',
      signature: 'Signature',
      issuer: tally_type,
      request: 'good',
      units: net,
      tally_uuid,
      chit_seq,
    };
    console.log("LOG_DATA ==> ", JSON.stringify(payload));

    insertChit(
      wm,
      payload,
    ).then((result) => {
      console.log("RESULT ==> ", result);
      Alert.alert("Success", "Chit payment success", [
        {
          text: "OK",
          onPress: () => {
            props.navigation.goBack();
          }
        }
      ]);
    }).catch(err => {
      console.log("ERROR ==> ", err);
      Alert.alert("Error", err.toString());
    }).finally(() => {
      setDisabled(false);
    });
  }

  if (loading) {
    return <View style={{ flex: 1, justifyContent: 'center', alignItems: 'center' }}>
      <ActivityIndicator size={"large"} />
    </View>
  }

  return <ScrollView
    style={styles.container}
    contentContainerStyle={styles.contentContainer}
  >
    <HelpText
      label={memoText?.title ?? ''}
      helpText={memoText?.help ?? ''}
      style={styles.headerText}
    />
    <TextInput
      style={styles.input}
      placeholder="Memo"
      value={memo}
      onChangeText={setMemo}
    />
    <HelpText
      label={referenceText?.title ?? ''}
      helpText={referenceText?.help ?? ''}
      style={styles.headerText}
    />
    <TextInput
      style={styles.input}
      placeholder="Reference"
      value={reference}
      onChangeText={setReference}
    />

    <HelpText
      label={netText?.title ?? ''}
      helpText={netText?.help ?? ''}
      style={styles.headerText}
    />
    <TextInput
      style={styles.input}
      placeholder="Enter amount"
      keyboardType="number-pad"
      value={chit}
      onChangeText={setChit}
    />
    {
      currencyCode && totalNetDollar ?
        <Text style={{ fontWeight: '500' }}>{currencyCode} {totalNetDollar}</Text> :
        <></>
    }
    <Button
      style={{ marginTop: 8, }}
      title="Make Payment"
      onPress={onMakePayment}
      disabled={disabled}
    />
  </ScrollView>
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
    margin: 16,
  },
  contentContainer: {
    flex: 1,
    padding: 16,
    backgroundColor: 'white'
  },
  input: {
    padding: 10,
    backgroundColor: colors.gray100,
    marginBottom: 16,
  },
  headerText: {
    color: colors.black,
    fontSize: 14,
  },
})

export default PaymentDetail;

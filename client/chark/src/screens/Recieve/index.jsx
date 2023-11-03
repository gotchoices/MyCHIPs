import React, { useEffect, useMemo, useRef, useState } from "react";
import {
  View,
  Text,
  Alert,
  TextInput,
  StyleSheet,
  ScrollView,
  TouchableOpacity,
  ActivityIndicator,
} from "react-native";
import { useSelector } from "react-redux";
import { Toast } from "react-native-toast-message/lib/src/Toast";
import { ChitIcon, SwapIcon } from "../../components/SvgAssets/SvgAssets";
import Button from "../../components/Button";
import { colors } from "../../config/constants";
import { getCurrency } from "../../services/profile";
import useSocket from "../../hooks/useSocket";
import { round } from "../../utils/common";

const Receive = (props) => {
  const [memo, setMemo] = useState("");
  const [reference, setReference] = useState("");
  const [chit, setChit] = useState("");
  const [usd, setUSD] = useState();

  const [loading, setLoading] = useState(false);
  const [disabled, setDisabled] = useState(false);

  const [isSwitched, setIsSwitched] = useState(false);

  const ref = useRef("");
  const { wm } = useSocket();

  const { preferredCurrency } = useSelector((state) => state.profile);
  const [conversionRate, setConversionRate] = useState(undefined);
  const currencyCode = preferredCurrency.code;

  useEffect(() => {
    if (currencyCode) {
      setLoading(true);
      getCurrency(wm, currencyCode)
        .then((data) => {
       
          setConversionRate(parseFloat(data?.rate ?? 1));
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

  const addReference = () => {};

  const onMakePayment = () => {
    props.navigation.navigate("ShareTally");
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
                <Text style={[styles.text, { marginLeft: 10 }]}>{chit}</Text>
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

      <TouchableOpacity onPress={addReference}>
        <Text style={styles.link}>Add Reference</Text>
      </TouchableOpacity>

      <View style={styles.buttonView}>
        <Button
          style={styles.button}
          title={"Receive"}
          onPress={onMakePayment}
          disabled={disabled}
        />
      </View>
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
  link: {
    color: colors.blue,
    alignSelf: "flex-end",
    textDecorationStyle: "solid",
    textDecorationLine: "underline",
  },
});

export default Receive;

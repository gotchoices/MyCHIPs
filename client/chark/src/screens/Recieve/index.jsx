import React, { useEffect, useRef, useState } from "react";
import {
  View,
  Text,
  TextInput,
  StyleSheet,
  ScrollView,
  TouchableOpacity,
  ActivityIndicator,
  Keyboard,
} from "react-native";
import { useSelector } from "react-redux";
import { ChitIcon, SwapIcon } from "../../components/SvgAssets/SvgAssets";
import Button from "../../components/Button";
import { colors } from "../../config/constants";
import { getCurrency } from "../../services/user";
import useSocket from "../../hooks/useSocket";
import { round } from "../../utils/common";
import { receiveChit } from '../../services/chit';
import { Toast } from "react-native-toast-message/lib/src/Toast";
import { useTallyText } from "../../hooks/useLanguage";

const Receive = (props) => {
  const [memo, setMemo] = useState("");
  const [chit, setChit] = useState("");
  const [usd, setUSD] = useState();

  const [loading, setLoading] = useState(false);
  const [disabled, setDisabled] = useState(false);
  const [inputWidth, setInputWidth] = useState(80);

  const [isSwitched, setIsSwitched] = useState(false); 
 
  const ref = useRef("");
  const { wm } = useSocket();

  const { request, comment } = useTallyText(wm);

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

  const onReceive = async () => {
    const net = round((chit ?? 0) * 1000, 0);

    if (net< 0) {
      return Toast.show({
        type: 'error',
        text1: "Can't input negative chit.",
      });
    }

    if (net== 0) {
      return Toast.show({
        type: 'error',
        text1: 'Please provide an amount',
      });
    }

    try {
      Keyboard.dismiss();
      setDisabled(true);
      const invoice = await receiveChit(wm, {
        memo,
        ref: {},
        units: chit,
        format: ['json', 'link'],
      })

      const json = invoice?.[0];
      const link = invoice?.[1];

      props.navigation.navigate('RequestShare', {
        json,
        link,
      });
    } catch(err) {
      console.log({err})
    } finally {
      setDisabled(false);
    }
  };

  /**
    * @param {string} type - chit or usd
    */
  const onAmountChange = (type) => {
    /**
      * @param {string} text - amount
      */
    return (text) => {
      const regex = /(\..*){2,}/;
      if(regex.test(text)) {
        return;
      }

      const textLength = text.length;
      setInputWidth(Math.max(Math.ceil(textLength * 20), 80))

      if(type === 'chit') {
        setChit(text);
        totalNetDollar(text);
      } else if(type === 'usd') {
        setUSD(text);
        totalChit(text);
      }
    }
  }

  const checkChipDecimalPlace = () => {
    let newValue = '';
    if(chit) {
      const [precision, decimalPlace] = chit.split('.');
      if(decimalPlace) {
        const decimalLength = decimalPlace.length;
        const remainingLength = Math.max(3 - decimalLength, 0);
        newValue = chit + Array(remainingLength).fill('0').join('');
        setChit(newValue)
      } else {
        newValue = precision + '.000'
        setChit(newValue);
      }
    }

    if(newValue) {
      setInputWidth(Math.max(Math.ceil(newValue.length * 20), 80))
    }
  }

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
      keyboardShouldPersistTaps="handled"
      contentContainerStyle={styles.contentContainer}
    >
      <View style={styles.centerWrapper}>
        {isSwitched ? (
          <>
            <View style={styles.row}>
              <Text style={styles.text}>USD</Text>
              <TextInput
                style={[styles.amount, { width: inputWidth }]}
                placeholder="0.00"
                keyboardType="numeric"
                value={usd}
                onChangeText={onAmountChange('usd')}
                onBlur={checkChipDecimalPlace}
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
                style={[styles.amount, { width: inputWidth }]}
                placeholder="0.00"
                keyboardType="numeric"
                value={chit}
                onChangeText={onAmountChange('chit')}
                onBlur={checkChipDecimalPlace}
              />
            </View>

            {currencyCode && usd ? (
               <View style={[styles.row,{alignSelf:'flex-end',marginRight:0}]}>
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
          placeholder={comment?.title ?? 'Comment'}
          value={memo}
          onChangeText={setMemo}
        />
      </TouchableOpacity>


      {/* <TouchableOpacity onPress={addReference}>
        <Text style={styles.link}>Add Reference</Text>
      </TouchableOpacity> */}


      <View style={styles.buttonView}>
        <Button
          style={styles.button}
          title={request?.title ?? 'Request'}
          onPress={onReceive}
          disabled={disabled}
        />
      </View>
    </ScrollView>
  );
};

const styles = StyleSheet.create({
  container: {
    flex: 1,
    paddingTop: 50,
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
    paddingHorizontal: 16,
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
    width:220,
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

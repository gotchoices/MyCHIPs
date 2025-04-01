import React, {useEffect, useState} from 'react';
import PropTypes from 'prop-types';
import { useSelector } from 'react-redux';
import {
  View,
  Text,
  TextInput,
  StyleSheet,
  TouchableOpacity,
  ActivityIndicator,
} from 'react-native';

import { ChitIcon, SwapIcon } from '../components/SvgAssets/SvgAssets';
import { colors } from '../config/constants';
import { getCurrency } from '../services/user';
import useSocket from '../hooks/useSocket';
import { round, formatChipValue } from '../utils/common';

const ChitInput = props => {
  const {wm} = useSocket();

  const chit = props.chit ?? ''
  const distributedPayment = props.distributedPayment;

  const [loading, setLoading] = useState(false);
  const [inputWidth, setInputWidth] = useState(80);

  const [isSwitched, setIsSwitched] = useState(false);

  const {preferredCurrency} = useSelector(state => state.profile);
  const [conversionRate, setConversionRate] = useState(undefined);

  const currencyCode = preferredCurrency.code;

  useEffect(() => {
    if (currencyCode) {
      setLoading(true);
      getCurrency(wm, currencyCode)
        .then(data => {
          setConversionRate(parseFloat(data?.rate ?? 1));
        })
        .catch(err => {
          console.log('EXCEPTION ==> ', err);
        })
        .finally(() => {
          setLoading(false);
        });
    }
  }, [currencyCode]);

  useEffect(() => {
    if(distributedPayment) {
      props.setChit(distributedPayment.units ?? 0)
      totalNetDollar(distributedPayment.units ?? 0)
      const textLength = distributedPayment?.units?.length;
      setInputWidth(Math.max(Math.ceil(textLength * 20), 80))
    }
  }, [distributedPayment])

  useEffect(() => {
    if(distributedPayment?.units) {
      totalNetDollar(distributedPayment.units ?? 0)
    }
  }, [distributedPayment?.units, conversionRate])

  const totalNetDollar = text => {
    const convertedChit = parseInt(text);
    if (conversionRate && convertedChit) {
      const total = convertedChit * conversionRate;
      const totalValue = round(total, 2);

      return props.setUSD(totalValue);
    }

    props.setUSD(0);
  };

  const totalChit = text => {
    const convertedUSD = parseInt(text);
    if (conversionRate && convertedUSD) {
      const total = convertedUSD / conversionRate;
      const totalValue = round(total, 2);

      return props.setChit(totalValue);
    }

    props.setChit(0);
  };

  /**
   * @param {string} type - chit or usd
   */
  const onAmountChange = type => {
    /**
     * @param {string} text - amount
     */
    return text => {
      props.setHasError(false);
      const regex = /(\..*){2,}/;
      if (regex.test(text)) {
        return;
      }

      const textLength = text.length;
      setInputWidth(Math.max(Math.ceil(textLength * 20), 80));

      if (type === 'chit') {
        props.setChit(text);
        totalNetDollar(text);
      } else if (type === 'usd') {
        props.setUSD(text);
        totalChit(text);
      }
    };
  };

  const checkChipDecimalPlace = () => {
    if (chit) {
      const formattedValue = formatChipValue(chit);
      props.setChit(formattedValue);
      setInputWidth(Math.max(Math.ceil(formattedValue.length * 20), 80));
    }
  };

  if (loading) {
    return (
      <View style={{ marginVertical: 10, justifyContent: 'center', alignItems: 'center'}}>
        <ActivityIndicator size={'large'} />
      </View>
    );
  }

  return (
    <>
      <View style={styles.centerWrapper}>
        {isSwitched ? (
          <>
            <View style={styles.row}>
              <Text style={[styles.text, props.hasError ? styles.errorInput : {}]}>USD</Text>
              <TextInput
                maxLength={12}
                style={[styles.amount, {width: inputWidth}, props.hasError ? styles.errorInput : {}]}
                placeholder="0.00"
                keyboardType="numeric"
                value={props.usd}
                onChangeText={onAmountChange('usd')}
                onBlur={checkChipDecimalPlace}
              />
            </View>

            {currencyCode && chit ? (
              <View
                style={[styles.row, {alignSelf: 'flex-end', marginRight: 20}]}>
                <ChitIcon color={colors.black} height={18} width={12} />
                <Text style={[styles.text, {marginLeft: 10}]}>{chit}</Text>
              </View>
            ) : (
              <></>
            )}
          </>
        ) : (
          <>
            <View style={styles.row}>
              <ChitIcon color={props.hasError ? colors.red : colors.black} height={18} width={12} />
              <TextInput
                maxLength={12}
                style={[styles.amount, {width: inputWidth}, props.hasError ? styles.errorInput : {}]}
                placeholder="0.00"
                keyboardType="numeric"
                value={chit}
                onChangeText={onAmountChange('chit')}
                onBlur={checkChipDecimalPlace}
              />
            </View>

            {currencyCode && props.usd ? (
              <View
                style={[styles.row, {alignSelf: 'flex-end', marginRight: 0}]}>
                <Text style={styles.text}>
                  {props.usd} {currencyCode}
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
          onPress={() => setIsSwitched(!isSwitched)}>
          <SwapIcon />
        </TouchableOpacity>
      ) : (
        <></>
      )}
    </>
  );
};

const styles = StyleSheet.create({
  amount: {
    paddingLeft: 10,
    fontSize: 26,
    paddingVertical: 20,
    fontWeight: '500',
    fontFamily: 'inter',
    color: colors.black,
  },
  centerWrapper: {
    marginBottom: 30,
    alignItems: 'center',
    justifyContent: 'center',
  },
  row: {
    width: 220,
    paddingRight: 20,
    flexDirection: 'row',
    alignItems: 'center',
    justifyContent: 'center',
  },
  text: {
    fontWeight: '500',
    color: colors.gray300,
  },
  icon: {
    position: 'absolute',
    right: 60,
    top: 40,
  },
  errorInput: {
    color: colors.red,
  },
});

ChitInput.propTypes = {
  chit: PropTypes.oneOfType([
    PropTypes.string,
    PropTypes.number,
  ]).isRequired,
  setChit: PropTypes.func.isRequired,
  usd: PropTypes.oneOfType([
    PropTypes.string,
    PropTypes.number,
  ]).isRequired,
  setUSD: PropTypes.func.isRequired,
  hasError: PropTypes.bool,
  setHasError: PropTypes.func,
  distributedPayment: PropTypes.any,
}

export default ChitInput;

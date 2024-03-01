import React, { useEffect, useState } from "react";
import { StyleSheet, View, findNodeHandle } from "react-native"
import { Picker } from '@react-native-picker/picker';
import AsyncStorage from "@react-native-async-storage/async-storage";
import { useSelector, useDispatch } from 'react-redux';

import Button from '../../../components/Button';
import HelpText from "../../../components/HelpText";

import { colors } from '../../../config/constants';
import useSocket from "../../../hooks/useSocket";
import { getCurrency } from '../../../services/currency';
import { setPreferredCurrency } from '../../../redux/profileSlice';

const Currency = (props) => {
  const [currency, setCurrency] = useState('');
  const [currencies, setCurrencies] = useState([]);
  const { wm } = useSocket();
  const { preferredCurrency } = useSelector(state => state.profile);
  const dispatch = useDispatch();

  useEffect(() => {
    getCurrency(wm).then((data) => {
      setCurrencies(data ?? []);
    }).catch(err => {
    })
  }, [setCurrencies])

  useEffect(() => {
    setCurrency(preferredCurrency.code);
  }, [preferredCurrency])

  const onSave = () => {
    if(currency === '') {
      dispatch(setPreferredCurrency({
        name: '',
        code: '',
      }))
      AsyncStorage.setItem("preferredCurrency", JSON.stringify({ cur_name: '', cur_code: '' }));
      props.onCancel();
      return;
    }
    const found = currencies.find((cur) => cur.cur_code === currency);
    if (found) {
      dispatch(setPreferredCurrency({
        name: found?.cur_name,
        code: found?.cur_code,
      }))
      AsyncStorage.setItem("preferredCurrency", JSON.stringify(found));
      props.onCancel();
    }
  }

  return (
    <View style={styles.container}>
      <View style={styles.header}>
        <HelpText style={{ color: colors.black }} label="Currency" />
      </View>

      <View style={styles.body}>
        <Picker
          style={styles.input}
          selectedValue={currency}
          mode="dropdown"
          onValueChange={(item) => {
            setCurrency(item)
          }}
        >
          <Picker.Item
            label="None"
            value=""
          />

          {
            currencies.map((currency) => (
              <Picker.Item
                key={currency.cur_code}
                label={currency.cur_name}
                value={currency.cur_code}
              />
            ))
          }
        </Picker>

        <View style={styles.action}>
          <View style={styles.actionItem}>
            <Button
              title="cancel_text"
              style={styles.cancel}
              onPress={props.onCancel}
              textColor={colors.blue}
            />
          </View>

          <View style={styles.actionItem}>
            <Button
              title="save_changes_text"
              onPress={onSave}
            />
          </View>
        </View>
      </View>
    </View>
  )
}

const styles = StyleSheet.create({
  container: {
    flex: 1
  },
  header: {
    padding: 10,
    marginBottom: 10,
    borderBottomWidth: 1,
    borderBottomColor: colors.lightgray,
  },
  body: {
    margin: 10,
  },
  input: {
    marginBottom: 16,
    backgroundColor: colors.antiflashwhite,
  },
  action: {
    flexDirection: 'row',
  },
  actionItem: {
    width: '48%',
  },
  cancel: {
    borderWidth: 1,
    borderColor: colors.blue,
    backgroundColor: colors.white,
    marginRight: '4%',
  },
})

export default Currency;

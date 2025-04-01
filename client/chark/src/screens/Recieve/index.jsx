import React, { useRef, useState } from 'react';
import {
  View,
  TextInput,
  StyleSheet,
  TouchableOpacity,
  Keyboard,
} from "react-native";
import { useSelector } from "react-redux";
import { KeyboardAwareScrollView } from 'react-native-keyboard-aware-scroll-view';

import Button from "../../components/Button";
import ChitInput from '../../components/ChitInput';

import { colors } from "../../config/constants";
import useSocket from "../../hooks/useSocket";
import { round, chipsToUnits } from "../../utils/common";
import { receiveChit } from '../../services/chit';
import { showError } from '../../utils/error';
import { useChitsMeText } from '../../hooks/useLanguage';
import useTitle from '../../hooks/useTitle';

const Receive = props => {
  const [memo, setMemo] = useState('');
  const [chit, setChit] = useState('');
  const [usd, setUSD] = useState('');
  const [chitInputError, setChitInputError] = useState(false);

  const [disabled, setDisabled] = useState(false);

  const ref = useRef('');
  const {wm} = useSocket();

  const chitsMeText = useChitsMeText(wm);

  useTitle(props.navigation, chitsMeText?.col?.request?.title)

  const onReceive = async () => {
    const net = chipsToUnits(chit);

    if (net <= 0) {
      return setChitInputError(true);
    }

    setChitInputError(false);

    try {
      Keyboard.dismiss();
      setDisabled(true);
      const invoice = await receiveChit(wm, {
        memo,
        ref: {},
        units: chit,
        format: ['json', 'link'],
      });

      const json = invoice?.[0];
      const link = invoice?.[1];

      props.navigation.navigate('RequestShare', {
        json,
        link,
      });
    } catch(err) {
      showError(err);
    } finally {
      setDisabled(false);
    }
  };

  return (
    <KeyboardAwareScrollView
      style={styles.container}
      enableOnAndroid
      keyboardShouldPersistTaps="handled"
      contentContainerStyle={styles.contentContainer}
    >
      <ChitInput
        chit={chit}
        setChit={setChit}
        usd={usd}
        setUSD={setUSD}
        hasError={chitInputError}
        setHasError={setChitInputError}
      />

      <TouchableOpacity
        style={styles.input}
        onPress={() => ref.current.focus()}>
        <TextInput
          ref={ref}
          placeholder={chitsMeText?.col?.memo?.title?? 'comment'}
          value={memo}
          onChangeText={setMemo}
        />
      </TouchableOpacity>

      <View style={styles.buttonView}>
        <Button
          style={styles.button}
          title={chitsMeText?.col?.request?.title ?? ''}
          onPress={onReceive}
          disabled={disabled}
        />
      </View>
    </KeyboardAwareScrollView>
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
    fontWeight: '500',
    fontFamily: 'inter',
    color: colors.black,
  },
  contentContainer: {
    flex: 1,
    paddingHorizontal: 16,
    backgroundColor: 'white',
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
    width: '100%',
    borderRadius: 40,
    marginBottom: 20,
    borderColor: 'blue',
    alignItems: 'center',
    justifyContent: 'center',
    backgroundColor: 'blue',
  },
  centerWrapper: {
    marginBottom: 30,
    alignItems: 'center',
    justifyContent: 'center',
  },
  buttonView: {
    flex: 1,
    justifyContent: 'flex-end',
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
  link: {
    color: colors.blue,
    alignSelf: 'flex-end',
    textDecorationStyle: 'solid',
    textDecorationLine: 'underline',
  },
  errorInput: {
    color: colors.red,
  },
});

export default Receive;

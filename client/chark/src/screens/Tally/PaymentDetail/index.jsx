import React, { useEffect, useRef, useState } from "react";
import { useDispatch } from 'react-redux';
import {
  StyleSheet,
  View,
  TextInput,
  TouchableOpacity,
  Keyboard,
} from "react-native";
import { v5 as uuidv5 } from 'uuid';
import stringify from 'json-stable-stringify';
import moment from 'moment';
import { KeyboardAwareScrollView } from 'react-native-keyboard-aware-scroll-view';

import { colors } from "../../../config/constants";
import Button from "../../../components/Button";
import useSocket from "../../../hooks/useSocket";
import { round } from "../../../utils/common";
import { insertChit } from "../../../services/tally";
import { useChitsMeText } from "../../../hooks/useLanguage";
import useMessageText from "../../../hooks/useMessageText";
import useTitle from '../../../hooks/useTitle';
import { showError } from '../../../utils/error';
import { createLiftsPay } from '../../../services/pay'

import { createSignature } from "../../../utils/message-signature";
import { setShowCreateSignatureModal } from '../../../redux/profileSlice';
import { KeyNotFoundError } from '../../../utils/Errors';

import BottomSheetModal from "../../../components/BottomSheetModal";
import SuccessModal from "../Success";
import { promptBiometrics } from "../../../services/biometrics";
import ChitInput from '../../../components/ChitInput';

const PaymentDetail = (props) => {
  const { chit_ent, tally_uuid, chit_seq, tally_type, chad, distributedPayment } = props.route?.params;
  const { wm } = useSocket();
  const dispatch = useDispatch();

  const [memo, setMemo] = useState();
  const [reference, setReference] = useState({});
  const [chit, setChit] = useState('');
  const [chitInputError, setChitInputError] = useState(false);

  const [usd, setUSD] = useState('');

  const [disabled, setDisabled] = useState(false);

  const [showSuccess, setShowSuccess] = useState(false);

  const ref = useRef("");

  const chitsText = useChitsMeText(wm);
  const { messageText } = useMessageText();

  const talliesMeMessageText = messageText?.tallies_v_me?.msg;

  const showCreateSignatureModal = () => {
    dispatch(setShowCreateSignatureModal(true));
  }

  useTitle(props.navigation, chitsText?.msg?.dirpmt?.title)

  useEffect(() => {
    if(distributedPayment) {
      setMemo(distributedPayment.memo ?? 0)
    }
  }, [distributedPayment])

  const onDistributedPayment = async () => {
    Keyboard.dismiss();
    setDisabled(true);

    try {
      const pay = await createLiftsPay(wm, {
        ...distributedPayment,
        units: chit,
        memo: memo,
      });

      setShowSuccess(true);
    } catch(err) {
      showError(err)
    } finally {
      setDisabled(false);
    }
  }

  const onMakePayment = async () => {
    Keyboard.dismiss();
    const net = round((chit ?? 0) * 1000, 0);

    if (net < 0) {
      return setChitInputError(true);
    }

    if (net == 0) {
      return setChitInputError(true);
    }

    setChitInputError(false);
    setDisabled(true);
    const _chad = `chip://${chad.cid}:${chad.agent}`
    const date = moment().format('YYYY-MM-DDTHH:mm:ss.SSSZ')
    const uuid = uuidv5(date + Math.random(), uuidv5(_chad, uuidv5.URL));
    const referenceJson = JSON.stringify({});

    const chitJson = {
      uuid,
      date,
      memo,
      units: net,
      by: tally_type,
      type: "tran",
      tally: tally_uuid,
      ref: reference,
    }

    try {
      const json = stringify(chitJson);

      await promptBiometrics("Use biometrics to create a signature")
      const signature = await createSignature(json)

      const payload = {
        chit_ent,
        chit_seq,
        memo,
        chit_date: date,
        signature,
        units: net,
        request: "good",
        issuer: tally_type,
        reference: referenceJson,
      };

      await insertChit(wm, payload)
      setShowSuccess(true);
    } catch(err) {
      if (err instanceof KeyNotFoundError) {
        showCreateSignatureModal();
      } else {
        showError(err);
      }
    } finally {
      setDisabled(false);
    }
  };

  const onPay = () => {
    if(distributedPayment) {
      onDistributedPayment()
    } else {
      onMakePayment()
    }
  }

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
        distributedPayment={distributedPayment}
      />

      <TouchableOpacity
        style={styles.input}
        onPress={() => ref.current.focus()}
      >
        <TextInput
          ref={ref}
          placeholder={chitsText?.col?.memo?.title ?? ''}
          value={memo}
          onChangeText={setMemo}
        />
      </TouchableOpacity>

      <View style={styles.buttonView}>
        <Button
          style={styles.button}
          title={talliesMeMessageText?.['launch.pay']?.title ?? ''}
          onPress={onPay}
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
    </KeyboardAwareScrollView>
  );
};

const styles = StyleSheet.create({
  container: {
    flex: 1,
    paddingTop: 50,
    paddingBottom: 10,
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
  errorInput: {
    color: colors.red,
  }
});

export default PaymentDetail;

import React, { useRef, useState } from 'react';
import {
  StyleSheet,
  View,
  TextInput,
  TouchableOpacity,
  Keyboard,
} from 'react-native';
import { v5 as uuidv5 } from 'uuid';
import moment from 'moment';
import { KeyboardAwareScrollView } from 'react-native-keyboard-aware-scroll-view';

import { colors } from '../../../config/constants';
import Button from '../../../components/Button';
import useSocket from '../../../hooks/useSocket';
import { round, chipsToUnits } from '../../../utils/common';
import {insertChit } from '../../../services/tally';
import {useChitsMeText} from '../../../hooks/useLanguage';
import useTitle from '../../../hooks/useTitle';
import { showError } from '../../../utils/error';

import BottomSheetModal from '../../../components/BottomSheetModal';
import SuccessModal from '../Success';
import ChitInput from '../../../components/ChitInput';

const RequestDetail = props => {
  const {tally_uuid, chit_seq, tally_type, editDetails} = props.route?.params;
  const {wm} = useSocket();
  const editNetValue = Math.abs?.(editDetails?.net);
  const [chitInputError, setChitInputError] = useState(false);

  const [memo, setMemo] = useState(editDetails?.memo ?? '');
  const [reference, setReference] = useState({});
  const [chit, setChit] = useState(
    editNetValue ? editNetValue?.toString() : '',
  );
  const [usd, setUSD] = useState('');

  const [disabled, setDisabled] = useState(false);
  const [showSuccess, setShowSuccess] = useState(false);

  const ref = useRef('');

  const chitsText = useChitsMeText(wm);

  useTitle(props.navigation, chitsText?.msg?.dirreq?.title)

  const onMakePayment = () => {
    const net = chipsToUnits(chit);

    if (net <= 0) {
      return setChitInputError(true);
    }

    setChitInputError(false);
    setDisabled(true);

    Keyboard.dismiss();
    const payload = {
      reference, // Pass reference object directly
      memo: memo,
      status: 'open',
      request: 'pend',
      issuer: tally_type === 'stock' ? 'foil' : 'stock',
      units: net,
      tally_uuid,
      chit_seq,
    };

    insertChit(wm, payload)
      .then(result => {
        console.log('RESULT ==> ', result);
        setShowSuccess(true);
      })
      .catch(err => {
        showError(err);
      })
      .finally(() => {
        setDisabled(false);
      });
  };

  return (
    <KeyboardAwareScrollView
      style={styles.container}
      enableOnAndroid
      extraHeight={150}
      extraScrollHeight={30}
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
          placeholder={chitsText?.col?.memo?.title ?? ''}
          value={reference}
          onChangeText={setMemo}
        />
      </TouchableOpacity>

      <View style={styles.buttonView}>
        <Button
          style={styles.button}
          title={editDetails ? 'Edit' : 'Request'}
          onPress={onMakePayment}
          disabled={disabled}
        />
      </View>

      <BottomSheetModal
        isVisible={showSuccess}
        onClose={() => setShowSuccess(false)}>
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
  contentContainer: {
    flex: 1,
    padding: 16,
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
    borderColor: colors.blue,
    alignItems: 'center',
    justifyContent: 'center',
    backgroundColor: colors.blue,
  },
  buttonView: {
    flex: 1,
    justifyContent: 'flex-end',
  },
  row: {
    width: 200,
    paddingRight: 20,
    flexDirection: 'row',
    alignItems: 'center',
    justifyContent: 'center',
  },
  text: {
    fontWeight: '500',
    color: colors.gray300,
  },
});

export default RequestDetail;

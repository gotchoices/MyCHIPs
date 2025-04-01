import React, { useEffect, useState } from 'react';
import { useDispatch } from 'react-redux';
import { StyleSheet, View, Alert } from 'react-native';
import { WebView } from 'react-native-webview';
import Toast from 'react-native-toast-message';
import stringify from 'json-stable-stringify';
import { v5 as uuidv5 } from 'uuid';
import { generateUuid, generateTimestamp } from '../../../utils/common';

import useSocket from '../../../hooks/useSocket';
import {  fetchTradingVariables } from '../../../services/tally';
import { insertChit } from '../../../services/chit';
import { parse } from '../../../utils/query-string';
import { createSignature } from '../../../utils/message-signature';
import { setShowCreateSignatureModal } from '../../../redux/profileSlice';
import { showError } from '../../../utils/error';
import useMessageText from '../../../hooks/useMessageText';
import useTitle from '../../../hooks/useTitle';
import { KeyNotFoundError } from '../../../utils/Errors';
import { toastVisibilityTime } from '../../../config/constants';
import { promptBiometrics } from '../../../services/biometrics';

const TradingVariables = (props) => {
  const { tally_seq, tally_ent, chad, tally_type, tally_uuid } = props.route?.params ?? {};
  const { wm } = useSocket();
  const dispatch = useDispatch();

  const { messageText } = useMessageText();
  const talliesMeMessageText = messageText?.tallies_v_me?.msg;
  const charkMessageText = messageText?.chark?.msg;

  const [trade, setTrade] = useState('');

  const showCreateSignatureModal = () => {
    dispatch(setShowCreateSignatureModal(true));
  }

  // Title
  useTitle(props.navigation, talliesMeMessageText?.trade?.title);

  useEffect(() => {
    fetchTradingVariables(wm, { tally_seq }).then((data) => {
      console.log(data, 'data')
      setTrade(data);
    }).catch(console.log)
  }, [wm, tally_seq, setTrade])

  const applySettings = async (request) => {
    const { target, bound, reward, clutch } = parse(request.url ?? '');

    const _chad = `chip://${chad.cuid}:${chad.agent}`
    const date = generateTimestamp();
    const uuid = generateUuid(tally_uuid, uuidv5.URL, _chad);

    const reference = {
      target,
      bound,
      reward,
      clutch,
    };

    const chitJson = {
      uuid,
      date,
      by: tally_type,
      type: "tran",
      tally: tally_uuid,
      ref: reference,
    }

    const message = stringify(chitJson);

    await promptBiometrics("Use biometrics to create a signature")
   
    createSignature(message).then((signature) => {
      const payload = {
        signature,
        reference,
        chit_type: 'set',
        chit_ent: tally_ent,
        chit_seq: tally_seq,
        chit_date: date, // Include date to ensure consistency with PaymentDetail
        units: null,
        issuer: tally_type,
        chit_uuid: uuid, // Include UUID to ensure DB doesn't generate a different one
      };

      return insertChit(wm, payload)
    }).then(() => {
      Toast.show({
        type: 'success',
        text1: charkMessageText?.updated?.help ?? '',
        visibilityTime: toastVisibilityTime,
      })
    }).catch((err) => {
      if(err instanceof KeyNotFoundError) {
        showCreateSignatureModal();
      } else {
        showError(err)
      }
    });

    return false;
  }

  return (
    <View style={styles.container}>
      <WebView
        startInLoadingState
        originWhitelist={["*"]}
        onShouldStartLoadWithRequest={applySettings}
        source={{ uri: trade }}
        injectedJavaScript={`
          const meta = document.createElement('meta'); 
          meta.setAttribute('content', 'width=device-width, initial-scale=1.0, maximum-scale=1.0, user-scalable=0'); 
          meta.setAttribute('name', 'viewport'); document.getElementsByTagName('head')[0].appendChild(meta); `
        }
      />
    </View>
  )

}

const styles = StyleSheet.create({
  container: {
    flex: 1,
  },
  action: {
    marginHorizontal: 10,
    marginVertical: 15,
  }
})

export default TradingVariables;

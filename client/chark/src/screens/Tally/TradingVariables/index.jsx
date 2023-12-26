import React, { useEffect, useState } from 'react';
import { useDispatch } from 'react-redux';
import { StyleSheet, View, Alert } from 'react-native';
import { WebView } from 'react-native-webview';
import Toast from 'react-native-toast-message';
import moment from 'moment';
import stringify from 'json-stable-stringify';
import { v5 as uuidv5 } from 'uuid';

import useSocket from '../../../hooks/useSocket';
import {  fetchTradingVariables } from '../../../services/tally';
import { insertChit } from '../../../services/chit';
import { parse } from '../../../utils/query-string';
import { createSignature } from '../../../utils/message-signature';
import { setShowCreateSignatureModal } from '../../../redux/profileSlice';

const TradingVariables = (props) => {
  const { tally_seq, tally_ent, chad, tally_type, tally_uuid } = props.route?.params ?? {};
  const { wm } = useSocket();
  const dispatch = useDispatch();

  const [trade, setTrade] = useState('');

  const showCreateSignatureModal = () => {
    dispatch(setShowCreateSignatureModal(true));
  }

  useEffect(() => {
    fetchTradingVariables(wm, { tally_seq }).then((data) => {
      console.log(data, 'data')
      setTrade(data);
    }).catch(console.log)
  }, [wm, tally_seq, setTrade])

  const applySettings = (request) => {
    const { target, bound, reward, clutch } = parse(request.url ?? '');

    const _chad = `chip://${chad.cid}:${chad.agent}`
    const date = moment().format('YYYY-MM-DDTHH:mm:ss.SSSZ')
    const uuid = uuidv5(date + Math.random(), uuidv5(_chad, uuidv5.URL));

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
    createSignature(message).then((signature) => {
      const payload = {
        signature,
        reference,
        chit_ent: tally_ent,
        chit_seq: tally_seq,
        units: null,
        issuer: tally_type,
      };

      insertChit(wm, payload).then(() => {
        Toast.show({
          type: 'success',
          text1: 'Settings applied successfully'
        })
      })
    }).catch((err) => {
      const { isKeyAvailable } = err;
      if (isKeyAvailable === false) {
        return Alert.alert(
          "Create Keys",
          "Seems like there is no key to create signature please continue to create one and offer tally.",
          [{ text: "Cancel" }, { text: "Continue", onPress: showCreateSignatureModal }]
        );
      }

      return Toast.show({
        type: 'error',
        text1: err.message,
      })
    });

    return false;
  }

  return (
    <View style={styles.container}>
      <WebView
        originWhitelist={["*"]}
        startInLoadingState
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

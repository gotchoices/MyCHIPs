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

  const applySettings = (request) => {
    try {
      const url = request.url || '';
      const parts = url.split('?');
      
      if (parts.length > 1) {
        const queryString = parts[1];
        const params = {};
        
        queryString.split('&').forEach(pair => {
          const [key, value] = pair.split('=');
          if (key && value !== undefined) {
            params[key] = value;
          }
        });
        
        // Extract and convert parameters to numbers
        const targetNum = parseFloat(params.target);
        const boundNum = parseFloat(params.bound);
        const rewardNum = parseFloat(params.reward);
        const clutchNum = parseFloat(params.clutch);
        
        // Build a reference object with the numeric values
        const reference = {
          target: targetNum,
          bound: boundNum,
          reward: rewardNum,
          clutch: clutchNum
        };
        
        // Create UUID and timestamp
        const _chad = `chip://${chad.cuid}:${chad.agent}`;
        const date = generateTimestamp();
        const uuid = generateUuid(tally_uuid, uuidv5.URL, _chad);
        
        // Create the chitJson object
        const chitJson = {
          uuid,
          date,
          by: tally_type,
          type: "tran",
          tally: tally_uuid,
          ref: reference,
        };
        
        // Stringify it for signing
        const message = stringify(chitJson);
        
        // Sign and submit as a chit
        (async () => {
          try {
            await promptBiometrics("Use biometrics to create a signature");
            const signature = await createSignature(message);
            
            const payload = {
              signature,
              reference,
              chit_type: 'set',
              chit_ent: tally_ent,
              chit_seq: tally_seq,
              chit_date: date,
              units: null,
              issuer: tally_type,
              chit_uuid: uuid,
              request: 'good', // Set request to 'good' like payment chits
            };
            
            await insertChit(wm, payload);
            
            Toast.show({
              type: 'success',
              text1: charkMessageText?.updated?.help ?? 'Trading variables updated',
              visibilityTime: toastVisibilityTime,
            });
          } catch (err) {
            if(err instanceof KeyNotFoundError) {
              showCreateSignatureModal();
            } else {
              showError(err);
            }
          }
        })();
      }
    } catch (error) {
      showError(error);
    }
    
    return false;
  };

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

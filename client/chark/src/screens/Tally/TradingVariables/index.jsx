import React, { useEffect, useState } from 'react';
import { StyleSheet, View, Dimensions } from 'react-native';
import { WebView } from 'react-native-webview';
import Button from '../../../components/Button';
import useSocket from '../../../hooks/useSocket';
import {  fetchTradingVariables } from '../../../services/tally';

const TradingVariables = (props) => {
  const { tally_seq } = props.route?.params ?? {};
  const { wm } = useSocket();

  const windowHeight = Dimensions.get('window').height;
  const [trade, setTrade] = useState('');

  useEffect(() => {
    fetchTradingVariables(wm, { tally_seq }).then((data) => {
      setTrade(data);
    }).catch(console.log)
  }, [wm, tally_seq, setTrade])

  return (
    <View style={styles.container}>
      <WebView
        startInLoadingState
        source={{
          html: `
          <html>
            <head>
              <meta name="viewport" content="width=device-width, initial-scale=1.0">
            </head>
            <body>
              <div style="padding-top: 20; height: ${windowHeight - 200}px">
                ${trade}
              <div>
            </body>
          </html>
        `}}
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

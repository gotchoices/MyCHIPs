import React, { useEffect, useState } from 'react';
import { StyleSheet, View } from 'react-native';
import { WebView } from 'react-native-webview';
import Button from '../../../components/Button';
import useSocket from '../../../hooks/useSocket';
import {  fetchTradingVariables } from '../../../services/tally';

const TradingVariables = () => {
  const { wm } = useSocket();

  const [trade, setTrade] = useState(null);

  useEffect(() => {
    fetchTradingVariables(wm).then((data) => {
      setTrade(data);
    }).catch(console.log)
  }, [])

  const onSubmit = () => {
    console.log('Submitted')
  }

  return (
    <View style={styles.container}>
      <WebView
        startInLoadingState
        source={{
          html: `
          <html>
            <head><meta name="viewport" content="width=device-width, initial-scale=1.0"></head>
            <body>
              <div style="padding-top: 20">
                ${trade}
              <div>
            </body>
          </html>
        `}}
      />

      <View style={styles.action}>
        <Button
          title="Submit"
          onPress={onSubmit}
        />
      </View>
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

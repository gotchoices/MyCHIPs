import React, { useState, useEffect } from 'react';
import { View, StyleSheet, TouchableWithoutFeedback, Text, Image } from 'react-native';
import { WebView } from 'react-native-webview';

import { random } from '../../../utils/common';
import useSocket from '../../../hooks/useSocket';
import constants, { colors } from '../../../config/constants';

import Header from '../Header';
import CustomText from '../../../components/CustomText';

import tabularBtn from '../../../../assets/tabular-button.png';

const TallyReport = (props) => {
  const [graph, setGraph] = useState();
  const { wm } = useSocket();

  useEffect(() => {
    const spec = {
      name:'graph',
      view:'mychips.users_v_me'
    }

    wm.request(`visual_balance_${random()}`, 'action', spec, data => {
      console.log('Graph data: ', data)
      setGraph(data);
    })
  }, [])

  const navigateBalanceSheet = () => {
    props.navigation.navigate('Home');
  }

  return (
    <View style={styles.container}>
      <View style={styles.header}>
        <Header
          icon={tabularBtn}
          title="Tally Report"
          onClick={navigateBalanceSheet}
        />
      </View>

      {
        graph && (
         <WebView
            source={{ html: `
              <html>
                <head><meta name="viewport" content="width=device-width, initial-scale=1.0"></head>
                <body>
                  <div style="display: flex; align-items: center; padding-top: 20">
                    ${graph}
                  </div>
                </body>
              </html>
            `}}
          />
        )
      }
    </View>
  )
}

const styles = StyleSheet.create({
  container: {
    flex: 1,
  },
  header: {
    backgroundColor: colors.gray700,
  },
  headerText: {
    color: colors.white,
  },
  reportView: {
  }
});


export default TallyReport;

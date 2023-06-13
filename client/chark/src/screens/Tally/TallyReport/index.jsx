import React, { useState, useEffect } from 'react';
import { View, StyleSheet } from 'react-native';
import { WebView } from 'react-native-webview';
import Toast from 'react-native-toast-message';

import useSocket from '../../../hooks/useSocket';
import { colors } from '../../../config/constants';
import { parse } from '../../../utils/query-string';
import { getTallyReport } from '../../../services/user';

import Header from '../Header';

import tabularBtn from '../../../../assets/tabular-button.png';

const TallyReport = (props) => {
  const [graph, setGraph] = useState();
  const { wm } = useSocket();

  useEffect(() => {
    getTallyReport(wm).then((data) => {
      setGraph(data);
    }).catch(err => {
      console.log('Error==> ', err)
      Toast.show({
        type: 'error',
        text1: err.message,
      })
    })
  }, [setGraph])

  const navigateBalanceSheet = () => {
    props.navigation.navigate('Home');
  }

  const interceptRequest = (request) => {
    const parsed = parse(request.url ?? '');

    const tally_seq = parsed.seq;
    const tally_ent = parsed.tally_ent;

    if (tally_seq) {
      props.navigation?.navigate?.('OpenTallyEdit', {
        tally_seq,
        tally_ent,
      });
    }

    // Intercepting requests with url having text seq
    return !request.url.includes('seq');
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
            onShouldStartLoadWithRequest={interceptRequest}
            originWhitelist={["*"]}
            source={{ uri: graph }}
            startInLoadingState
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

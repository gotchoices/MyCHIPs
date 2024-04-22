import React, { useState, useEffect } from 'react';
import { View, StyleSheet } from 'react-native';
import { WebView } from 'react-native-webview';

import useSocket from '../../../hooks/useSocket';
import { colors } from '../../../config/constants';
import { parse } from '../../../utils/query-string';
import { getTallyReport } from '../../../services/user';
import useMessageText from '../../../hooks/useMessageText';
import Header from "../Header";
import Activity from '../Activity';
import { showError } from '../../../utils/error';

import { TabularIcon } from '../../../components/SvgAssets/SvgAssets';

const TallyReport = (props) => {
  const [graph, setGraph] = useState();
  const { wm } = useSocket();
  const { messageText } = useMessageText();
  const charkText = messageText?.chark?.msg;

  useEffect(() => {
    getTallyReport(wm).then((data) => {
      setGraph(data);
    }).catch(err => {
      showError(err);
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
      <Header
        leftIcon={<TabularIcon />}
        title={charkText?.mychips?.title ?? ''}
        onClick={navigateBalanceSheet}
        onNavigateToNotification={() => {}}
        rightIcon={<Activity />}
      />

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
    marginTop: -10,
    marginHorizontal: 10,
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
